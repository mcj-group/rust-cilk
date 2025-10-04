//! A `MutVisitor` represents an AST modification; it accepts an AST piece and
//! mutates it in place. So, for instance, macro expansion is a `MutVisitor`
//! that walks over an AST and modifies it.
//!
//! Note: using a `MutVisitor` (other than the `MacroExpander` `MutVisitor`) on
//! an AST before macro expansion is probably a bad idea. For instance,
//! a `MutVisitor` renaming item names in a module will miss all of those
//! that are created by the expansion of a macro.

use std::ops::DerefMut;
use std::panic;

use rustc_data_structures::flat_map_in_place::FlatMapInPlace;
use rustc_span::source_map::Spanned;
use rustc_span::{Ident, Span, Symbol};
use smallvec::{SmallVec, smallvec};
use thin_vec::ThinVec;
use super::ResolverAstLoweringExt;

use crate::ast::*;
use crate::tokenstream::*;
use crate::visit::{AssocCtxt, BoundKind, FnCtxt, LifetimeCtxt, VisitorResult, try_visit};

mod sealed {
    use rustc_ast_ir::visit::VisitorResult;

    /// This is for compatibility with the regular `Visitor`.
    pub trait MutVisitorResult {
        type Result: VisitorResult;
    }

    impl<T> MutVisitorResult for T {
        type Result = ();
    }
}

use sealed::MutVisitorResult;

pub(crate) trait MutVisitable<V: MutVisitor> {
    type Extra: Copy;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra);
}

impl<V: MutVisitor, T: ?Sized> MutVisitable<V> for Box<T>
where
    T: MutVisitable<V>,
{
    type Extra = T::Extra;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        (**self).visit_mut(visitor, extra)
    }
}

impl<V: MutVisitor, T> MutVisitable<V> for Option<T>
where
    T: MutVisitable<V>,
{
    type Extra = T::Extra;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        if let Some(this) = self {
            this.visit_mut(visitor, extra)
        }
    }
}

impl<V: MutVisitor, T> MutVisitable<V> for Spanned<T>
where
    T: MutVisitable<V>,
{
    type Extra = T::Extra;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        let Spanned { span, node } = self;
        span.visit_mut(visitor, ());
        node.visit_mut(visitor, extra);
    }
}

impl<V: MutVisitor, T> MutVisitable<V> for [T]
where
    T: MutVisitable<V>,
{
    type Extra = T::Extra;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        for item in self {
            item.visit_mut(visitor, extra);
        }
    }
}

impl<V: MutVisitor, T> MutVisitable<V> for Vec<T>
where
    T: MutVisitable<V>,
{
    type Extra = T::Extra;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        for item in self {
            item.visit_mut(visitor, extra);
        }
    }
}

impl<V: MutVisitor, T> MutVisitable<V> for (T,)
where
    T: MutVisitable<V>,
{
    type Extra = T::Extra;
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        self.0.visit_mut(visitor, extra);
    }
}

impl<V: MutVisitor, T1, T2> MutVisitable<V> for (T1, T2)
where
    T1: MutVisitable<V, Extra = ()>,
    T2: MutVisitable<V, Extra = ()>,
{
    type Extra = ();
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        self.0.visit_mut(visitor, extra);
        self.1.visit_mut(visitor, extra);
    }
}

impl<V: MutVisitor, T1, T2, T3> MutVisitable<V> for (T1, T2, T3)
where
    T1: MutVisitable<V, Extra = ()>,
    T2: MutVisitable<V, Extra = ()>,
    T3: MutVisitable<V, Extra = ()>,
{
    type Extra = ();
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        self.0.visit_mut(visitor, extra);
        self.1.visit_mut(visitor, extra);
        self.2.visit_mut(visitor, extra);
    }
}

impl<V: MutVisitor, T1, T2, T3, T4> MutVisitable<V> for (T1, T2, T3, T4)
where
    T1: MutVisitable<V, Extra = ()>,
    T2: MutVisitable<V, Extra = ()>,
    T3: MutVisitable<V, Extra = ()>,
    T4: MutVisitable<V, Extra = ()>,
{
    type Extra = ();
    fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
        self.0.visit_mut(visitor, extra);
        self.1.visit_mut(visitor, extra);
        self.2.visit_mut(visitor, extra);
        self.3.visit_mut(visitor, extra);
    }
}

pub trait MutWalkable<V: MutVisitor> {
    fn walk_mut(&mut self, visitor: &mut V);
}

macro_rules! visit_visitable {
    (mut $visitor:expr, $($expr:expr),* $(,)?) => {{
        $(MutVisitable::visit_mut($expr, $visitor, ());)*
    }};
}

macro_rules! visit_visitable_with {
    (mut $visitor:expr, $expr:expr, $extra:expr $(,)?) => {
        MutVisitable::visit_mut($expr, $visitor, $extra)
    };
}

macro_rules! walk_walkable {
    ($visitor:expr, $expr:expr, mut) => {
        MutWalkable::walk_mut($expr, $visitor)
    };
}

macro_rules! impl_visitable {
    (|&mut $self:ident: $self_ty:ty,
      $vis:ident: &mut $vis_ty:ident,
      $extra:ident: $extra_ty:ty| $block:block) => {
        #[allow(unused_parens, non_local_definitions)]
        impl<$vis_ty: MutVisitor> MutVisitable<$vis_ty> for $self_ty {
            type Extra = $extra_ty;
            fn visit_mut(&mut $self, $vis: &mut $vis_ty, $extra: Self::Extra) -> V::Result {
                $block
            }
        }
    };
}

macro_rules! impl_walkable {
    ($(<$K:ident: $Kb:ident>)? |&mut $self:ident: $self_ty:ty,
      $vis:ident: &mut $vis_ty:ident| $block:block) => {
        #[allow(unused_parens, non_local_definitions)]
        impl<$($K: $Kb,)? $vis_ty: MutVisitor> MutWalkable<$vis_ty> for $self_ty {
            fn walk_mut(&mut $self, $vis: &mut $vis_ty) -> V::Result {
                $block
            }
        }
    };
}

macro_rules! impl_visitable_noop {
    (<mut> $($ty:ty,)*) => {
        $(
            impl_visitable!(|&mut self: $ty, _vis: &mut V, _extra: ()| {});
        )*
    };
}

macro_rules! impl_visitable_list {
    (<mut> $($ty:ty,)*) => {
        $(impl<V: MutVisitor, T> MutVisitable<V> for $ty
        where
            for<'a> &'a mut $ty: IntoIterator<Item = &'a mut T>,
            T: MutVisitable<V>,
        {
            type Extra = <T as MutVisitable<V>>::Extra;

            #[inline]
            fn visit_mut(&mut self, visitor: &mut V, extra: Self::Extra) {
                for i in self {
                    i.visit_mut(visitor, extra);
                }
            }
        })*
    }
}

macro_rules! impl_visitable_direct {
    (<mut> $($ty:ty,)*) => {
        $(impl_visitable!(
            |&mut self: $ty, visitor: &mut V, _extra: ()| {
                MutWalkable::walk_mut(self, visitor)
            }
        );)*
    }
}

macro_rules! impl_visitable_calling_walkable {
    (<mut>
        $( fn $method:ident($ty:ty $(, $extra_name:ident: $extra_ty:ty)?); )*
    ) => {
        $(fn $method(&mut self, node: &mut $ty $(, $extra_name:$extra_ty)?) {
            impl_visitable!(|&mut self: $ty, visitor: &mut V, extra: ($($extra_ty)?)| {
                let ($($extra_name)?) = extra;
                visitor.$method(self $(, $extra_name)?);
            });
            walk_walkable!(self, node, mut)
        })*
    }
}

macro_rules! define_named_walk {
    ((mut) $Visitor:ident
        $( pub fn $method:ident($ty:ty); )*
    ) => {
        $(pub fn $method<V: $Visitor>(visitor: &mut V, node: &mut $ty) {
            walk_walkable!(visitor, node, mut)
        })*
    };
}

super::common_visitor_and_walkers!((mut) MutVisitor);

macro_rules! generate_flat_map_visitor_fns {
    ($($name:ident, $Ty:ty, $flat_map_fn:ident$(, $param:ident: $ParamTy:ty)*;)+) => {
        $(
            #[allow(unused_parens)]
            impl<V: MutVisitor> MutVisitable<V> for ThinVec<$Ty> {
                type Extra = ($($ParamTy),*);

                #[inline]
                fn visit_mut(
                    &mut self,
                    visitor: &mut V,
                    ($($param),*): Self::Extra,
                ) -> V::Result {
                    $name(visitor, self $(, $param)*)
                }
            }

            fn $name<V: MutVisitor>(
                vis: &mut V,
                values: &mut ThinVec<$Ty>,
                $(
                    $param: $ParamTy,
                )*
            ) {
                values.flat_map_in_place(|value| vis.$flat_map_fn(value$(,$param)*));
            }
        )+
    }
}

generate_flat_map_visitor_fns! {
    visit_items, Box<Item>, flat_map_item;
    visit_foreign_items, Box<ForeignItem>, flat_map_foreign_item;
    visit_generic_params, GenericParam, flat_map_generic_param;
    visit_stmts, Stmt, flat_map_stmt;
    visit_exprs, Box<Expr>, filter_map_expr;
    visit_expr_fields, ExprField, flat_map_expr_field;
    visit_pat_fields, PatField, flat_map_pat_field;
    visit_variants, Variant, flat_map_variant;
    visit_assoc_items, Box<AssocItem>, flat_map_assoc_item, ctxt: AssocCtxt;
    visit_where_predicates, WherePredicate, flat_map_where_predicate;
    visit_params, Param, flat_map_param;
    visit_field_defs, FieldDef, flat_map_field_def;
    visit_arms, Arm, flat_map_arm;
}

pub fn walk_flat_map_pat_field<T: MutVisitor>(
    vis: &mut T,
    mut fp: PatField,
) -> SmallVec<[PatField; 1]> {
    vis.visit_pat_field(&mut fp);
    smallvec![fp]
}

macro_rules! generate_walk_flat_map_fns {
    ($($fn_name:ident($Ty:ty$(,$extra_name:ident: $ExtraTy:ty)*) => $visit_fn_name:ident;)+) => {$(
        pub fn $fn_name<V: MutVisitor>(vis: &mut V, mut value: $Ty$(,$extra_name: $ExtraTy)*) -> SmallVec<[$Ty; 1]> {
            vis.$visit_fn_name(&mut value$(,$extra_name)*);
            smallvec![value]
        }
    )+};
}

generate_walk_flat_map_fns! {
    walk_flat_map_arm(Arm) => visit_arm;
    walk_flat_map_variant(Variant) => visit_variant;
    walk_flat_map_param(Param) => visit_param;
    walk_flat_map_generic_param(GenericParam) => visit_generic_param;
    walk_flat_map_where_predicate(WherePredicate) => visit_where_predicate;
    walk_flat_map_field_def(FieldDef) => visit_field_def;
    walk_flat_map_expr_field(ExprField) => visit_expr_field;
    walk_flat_map_item(Box<Item>) => visit_item;
    walk_flat_map_foreign_item(Box<ForeignItem>) => visit_foreign_item;
    walk_flat_map_assoc_item(Box<AssocItem>, ctxt: AssocCtxt) => visit_assoc_item;
}

pub fn walk_filter_map_expr<T: MutVisitor>(vis: &mut T, mut e: Box<Expr>) -> Option<Box<Expr>> {
    vis.visit_expr(&mut e);
    Some(e)
}

pub fn walk_flat_map_stmt<T: MutVisitor>(
    vis: &mut T,
    Stmt { kind, span, mut id }: Stmt,
) -> SmallVec<[Stmt; 1]> {
    vis.visit_id(&mut id);
    let mut stmts: SmallVec<[Stmt; 1]> = walk_flat_map_stmt_kind(vis, kind)
        .into_iter()
        .map(|kind| Stmt { id, kind, span })
        .collect();
    match &mut stmts[..] {
        [] => {}
        [stmt] => vis.visit_span(&mut stmt.span),
        _ => panic!(
            "cloning statement `NodeId`s is prohibited by default, \
             the visitor should implement custom statement visiting"
        ),
    }
    stmts
}

fn walk_flat_map_stmt_kind<T: MutVisitor>(vis: &mut T, kind: StmtKind) -> SmallVec<[StmtKind; 1]> {
    match kind {
        StmtKind::Let(mut local) => smallvec![StmtKind::Let({
            vis.visit_local(&mut local);
            local
        })],
        StmtKind::Item(item) => vis.flat_map_item(item).into_iter().map(StmtKind::Item).collect(),
        StmtKind::Expr(expr) => vis.filter_map_expr(expr).into_iter().map(StmtKind::Expr).collect(),
        StmtKind::Semi(expr) => vis.filter_map_expr(expr).into_iter().map(StmtKind::Semi).collect(),
        StmtKind::Empty => smallvec![StmtKind::Empty],
        StmtKind::MacCall(mut mac) => {
            let MacCallStmt { mac: mac_, style: _, attrs, tokens: _ } = mac.deref_mut();
            for attr in attrs {
                vis.visit_attribute(attr);
            }
            vis.visit_mac_call(mac_);
            smallvec![StmtKind::MacCall(mac)]
        }
    }
}

pub fn noop_visit_vis<T: MutVisitor>(visibility: &mut Visibility, vis: &mut T) {
    match &mut visibility.kind {
        VisibilityKind::Public | VisibilityKind::Inherited => {}
        VisibilityKind::Restricted { path, id, shorthand: _ } => {
            vis.visit_path(path);
            vis.visit_id(id);
        }
    }
    vis.visit_span(&mut visibility.span);
}

pub fn noop_visit_capture_by<T: MutVisitor>(capture_by: &mut CaptureBy, vis: &mut T) {
    match capture_by {
        CaptureBy::Ref => {}
        CaptureBy::Value { move_kw } => {
            vis.visit_span(move_kw);
        }
    }
}

/// Some value for the AST node that is valid but possibly meaningless.
pub trait DummyAstNode {
    fn dummy() -> Self;
}

impl<T> DummyAstNode for Option<T> {
    fn dummy() -> Self {
        Default::default()
    }
}

impl<T: DummyAstNode + 'static> DummyAstNode for P<T> {
    fn dummy() -> Self {
        P(DummyAstNode::dummy())
    }
}

impl DummyAstNode for Item {
    fn dummy() -> Self {
        Item {
            attrs: Default::default(),
            id: DUMMY_NODE_ID,
            span: Default::default(),
            vis: Visibility {
                kind: VisibilityKind::Public,
                span: Default::default(),
                tokens: Default::default(),
            },
            ident: Ident::empty(),
            kind: ItemKind::ExternCrate(None),
            tokens: Default::default(),
        }
    }
}

impl DummyAstNode for Expr {
    fn dummy() -> Self {
        Expr {
            id: DUMMY_NODE_ID,
            kind: ExprKind::Err,
            span: Default::default(),
            attrs: Default::default(),
            tokens: Default::default(),
        }
    }
}

impl DummyAstNode for Ty {
    fn dummy() -> Self {
        Ty {
            id: DUMMY_NODE_ID,
            kind: TyKind::Err,
            span: Default::default(),
            tokens: Default::default(),
        }
    }
}

impl DummyAstNode for Pat {
    fn dummy() -> Self {
        Pat {
            id: DUMMY_NODE_ID,
            kind: PatKind::Wild,
            span: Default::default(),
            tokens: Default::default(),
        }
    }
}

impl DummyAstNode for Stmt {
    fn dummy() -> Self {
        Stmt { id: DUMMY_NODE_ID, kind: StmtKind::Empty, span: Default::default() }
    }
}

impl DummyAstNode for Block {
    fn dummy() -> Self {
        Block {
            stmts: Default::default(),
            id: DUMMY_NODE_ID,
            rules: BlockCheckMode::Default,
            span: Default::default(),
            tokens: Default::default(),
            could_be_bare_literal: Default::default(),
        }
    }
}

impl DummyAstNode for Crate {
    fn dummy() -> Self {
        Crate {
            attrs: Default::default(),
            items: Default::default(),
            spans: Default::default(),
            id: DUMMY_NODE_ID,
            is_placeholder: Default::default(),
        }
    }
}

impl<N: DummyAstNode, T: DummyAstNode> DummyAstNode for crate::ast_traits::AstNodeWrapper<N, T> {
    fn dummy() -> Self {
        crate::ast_traits::AstNodeWrapper::new(N::dummy(), T::dummy())
    }
}

struct ReplaceVariable {
    target_ident: Ident,
    target_id: NodeId,
    new_ident: Ident,
    new_id: NodeId,
    new_path_id: NodeId,
}

impl ReplaceVariable {
    fn visit_path_2(&mut self, Path { segments, span, tokens: _ }: &mut Path, e: &mut Expr) {
        self.visit_span(span); 
        println!("ReplaceVariable visit_path");
        for PathSegment { ident, id, args: _ } in segments {
            if ident.name == self.target_ident.name {
                println!("found target PathSegment {:?}", self.target_id);
                *ident = self.new_ident;
                *id = self.new_id;
                e.id = self.new_path_id;
            }
            // self.visit_ident(ident);
            // self.visit_id(id);
            // self.visit_opt(args, |args| vis.visit_generic_args(args)); // TODO: maybe I need to visit the args
        }
        // visit_lazy_tts(tokens, vis); // TODO: maybe I need to visit the tokens
    }

    fn noop_visit_expr_2(
        e: &mut Expr,
        vis: &mut ReplaceVariable,
    ) {
        let Expr { kind, id, span, attrs, tokens } = e;
        match kind {
            ExprKind::Array(exprs) => visit_thin_exprs(exprs, vis),
            ExprKind::ConstBlock(anon_const) => {
                vis.visit_anon_const(anon_const);
            }
            ExprKind::Repeat(expr, count) => {
                vis.visit_expr(expr);
                vis.visit_anon_const(count);
            }
            ExprKind::Tup(exprs) => visit_thin_exprs(exprs, vis),
            ExprKind::Call(f, args) => {
                vis.visit_expr(f);
                visit_thin_exprs(args, vis);
            }
            ExprKind::MethodCall(box MethodCall {
                seg: PathSegment { ident, id, args: seg_args },
                receiver,
                args: call_args,
                span,
            }) => {
                vis.visit_ident(ident);
                vis.visit_id(id);
                visit_opt(seg_args, |args| vis.visit_generic_args(args));
                vis.visit_method_receiver_expr(receiver);
                visit_thin_exprs(call_args, vis);
                vis.visit_span(span);
            }
            ExprKind::Binary(_binop, lhs, rhs) => {
                vis.visit_expr(lhs);
                vis.visit_expr(rhs);
            }
            ExprKind::Unary(_unop, ohs) => vis.visit_expr(ohs),
            ExprKind::Cast(expr, ty) => {
                vis.visit_expr(expr);
                vis.visit_ty(ty);
            }
            ExprKind::Type(expr, ty) => {
                vis.visit_expr(expr);
                vis.visit_ty(ty);
            }
            ExprKind::AddrOf(_, _, ohs) => vis.visit_expr(ohs),
            ExprKind::Let(pat, scrutinee, _, _) => {
                vis.visit_pat(pat);
                vis.visit_expr(scrutinee);
            }
            ExprKind::If(cond, tr, fl) => {
                vis.visit_expr(cond);
                vis.visit_block(tr);
                visit_opt(fl, |fl| ensure_sufficient_stack(|| vis.visit_expr(fl)));
            }
            ExprKind::While(cond, body, label) => {
                vis.visit_expr(cond);
                vis.visit_block(body);
                visit_opt(label, |label| vis.visit_label(label));
            }
            ExprKind::ForLoop { pat, iter, body, label, kind: _ } => {
                vis.visit_pat(pat);
                vis.visit_expr(iter);
                vis.visit_block(body);
                visit_opt(label, |label| vis.visit_label(label));
            }
            ExprKind::Loop(body, label, span) => {
                vis.visit_block(body);
                visit_opt(label, |label| vis.visit_label(label));
                vis.visit_span(span);
            }
            ExprKind::Match(expr, arms) => {
                vis.visit_expr(expr);
                arms.flat_map_in_place(|arm| vis.flat_map_arm(arm));
            }
            ExprKind::Closure(box Closure {
                binder,
                capture_clause,
                constness,
                coroutine_kind,
                movability: _,
                fn_decl,
                body,
                fn_decl_span,
                fn_arg_span,
            }) => {
                vis.visit_closure_binder(binder);
                visit_constness(constness, vis);
                coroutine_kind.as_mut().map(|coroutine_kind| vis.visit_coroutine_kind(coroutine_kind));
                vis.visit_capture_by(capture_clause);
                vis.visit_fn_decl(fn_decl);
                vis.visit_expr(body);
                vis.visit_span(fn_decl_span);
                vis.visit_span(fn_arg_span);
            }
            ExprKind::Block(blk, label) => {
                vis.visit_block(blk);
                visit_opt(label, |label| vis.visit_label(label));
            }
            ExprKind::Gen(_capture_by, body, _) => {
                vis.visit_block(body);
            }
            ExprKind::Await(expr, await_kw_span) => {
                vis.visit_expr(expr);
                vis.visit_span(await_kw_span);
            }
            ExprKind::Assign(el, er, span) => {
                vis.visit_expr(el);
                vis.visit_expr(er);
                vis.visit_span(span);
            }
            ExprKind::AssignOp(_op, el, er) => {
                vis.visit_expr(el);
                vis.visit_expr(er);
            }
            ExprKind::Field(el, ident) => {
                vis.visit_expr(el);
                vis.visit_ident(ident);
            }
            ExprKind::Index(el, er, brackets_span) => {
                vis.visit_expr(el);
                vis.visit_expr(er);
                vis.visit_span(brackets_span);
            }
            ExprKind::Range(e1, e2, _lim) => {
                visit_opt(e1, |e1| vis.visit_expr(e1));
                visit_opt(e2, |e2| vis.visit_expr(e2));
            }
            ExprKind::Underscore => {}
            ExprKind::Path(qself, path) => {
                vis.visit_qself(qself);
                vis.visit_path_2(path, e);
            }
            ExprKind::Break(label, expr) => {
                visit_opt(label, |label| vis.visit_label(label));
                visit_opt(expr, |expr| vis.visit_expr(expr));
            }
            ExprKind::Continue(label) => {
                visit_opt(label, |label| vis.visit_label(label));
            }
            ExprKind::Ret(expr) => {
                visit_opt(expr, |expr| vis.visit_expr(expr));
            }
            ExprKind::Yeet(expr) => {
                visit_opt(expr, |expr| vis.visit_expr(expr));
            }
            ExprKind::Become(expr) => vis.visit_expr(expr),
            ExprKind::InlineAsm(asm) => vis.visit_inline_asm(asm),
            ExprKind::FormatArgs(fmt) => vis.visit_format_args(fmt),
            ExprKind::OffsetOf(container, fields) => {
                vis.visit_ty(container);
                for field in fields.iter_mut() {
                    vis.visit_ident(field);
                }
            }
            ExprKind::MacCall(mac) => vis.visit_mac_call(mac),
            ExprKind::Struct(se) => {
                let StructExpr { qself, path, fields, rest } = se.deref_mut();
                vis.visit_qself(qself);
                vis.visit_path(path);
                fields.flat_map_in_place(|field| vis.flat_map_expr_field(field));
                match rest {
                    StructRest::Base(expr) => vis.visit_expr(expr),
                    StructRest::Rest(_span) => {}
                    StructRest::None => {}
                }
            }
            ExprKind::Paren(expr) => {
                vis.visit_expr(expr);
            }
            ExprKind::Yield(expr) => {
                visit_opt(expr, |expr| vis.visit_expr(expr));
            }
            ExprKind::Try(expr) => vis.visit_expr(expr),
            ExprKind::TryBlock(body) => vis.visit_block(body),
            ExprKind::CilkSpawn(body) => vis.visit_block(body),
            ExprKind::CilkScope(body) => vis.visit_block(body),
            ExprKind::Lit(_) | ExprKind::IncludedBytes(..) | ExprKind::CilkSync | ExprKind::Err => {}
        }
        vis.visit_id(id);
        vis.visit_span(span);
        visit_attrs(attrs, vis);
        visit_lazy_tts(tokens, vis);
    }
}

impl MutVisitor for ReplaceVariable {
    fn visit_expr(&mut self, e: &mut P<Expr>) {
        ReplaceVariable::noop_visit_expr_2(e, self);
    }
}
