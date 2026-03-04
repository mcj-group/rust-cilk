use crate::spec::base::apple::{Arch, TargetEnv, base};
use crate::spec::{Os, SanitizerSet, LinkerFlavor, Cc, Lld, Target, TargetMetadata, TargetOptions};
use std::path::PathBuf;

// Read the environment variable OPENCILK_RT_SEARCH_DIR to get the path to the OpenCilk runtime for
// this target.
// FIXME(jhilton): we should have default search paths for this so that we don't need to bother with
// having users set an environment variable.
fn opencilk_runtime_search_directory() -> PathBuf {
    let path = std::env::var("OPENCILK_RT_SEARCH_DIR").expect("OPENCILK_RT_SEARCH_DIR must be set");
    PathBuf::from(path)
}

pub(crate) fn target() -> Target {
    let (opts, llvm_target, arch) = base(Os::MacOs, Arch::Arm64, TargetEnv::Normal);
    let mut late_link_args = std::collections::BTreeMap::new();
    let opencilk_runtime_path = opencilk_runtime_search_directory()
        .into_os_string()
        .into_string()
        .expect("OpenCilk runtime path should contain only valid unicode!");
    let set_rpath = format!("-Wl,-rpath,{}", opencilk_runtime_path);
    let args_to_link_opencilk: Vec<std::borrow::Cow<'static, str>> = vec![
        "-L".into(),
        opencilk_runtime_path.into(),
        "-lopencilk_osx_dynamic".into(),
        set_rpath.into(),
    ];
    late_link_args.insert(LinkerFlavor::Darwin(Cc::Yes, Lld::No), args_to_link_opencilk.clone());
    Target {
        llvm_target,
        metadata: TargetMetadata {
            description: Some("ARM64 Apple macOS (11.0+, Big Sur+)".into()),
            tier: Some(1),
            host_tools: Some(true),
            std: Some(true),
        },
        pointer_width: 64,
        data_layout: "e-m:o-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-n32:64-S128-Fn32"
            .into(),
        arch,
        options: TargetOptions {
            mcount: "\u{1}mcount".into(),
            cpu: "apple-m1".into(),
            max_atomic_width: Some(128),
            // FIXME: The leak sanitizer currently fails the tests, see #88132.
            supported_sanitizers: SanitizerSet::ADDRESS
                | SanitizerSet::CFI
                | SanitizerSet::THREAD
                | SanitizerSet::REALTIME,
            supports_xray: true,
            late_link_args,
            ..opts
        },
    }
}
