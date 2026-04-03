use std::env;
use std::path::PathBuf;
use std::process::Command;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-changed=proofs/dafny/executable/SchedulePlannerKernel.dfy");
    println!("cargo:rerun-if-changed=proofs/dafny/executable/RuntimeStateKernel.dfy");
    println!("cargo:rerun-if-changed=proofs/dafny/executable/TimeoutBatchKernel.dfy");

    let out_dir = PathBuf::from(env::var("OUT_DIR").expect("OUT_DIR not set"));
    let planner_path = out_dir.join("dafny-schedule-planner");
    let runtime_kernel_path = out_dir.join("dafny-runtime-kernel");
    let timeout_kernel_path = out_dir.join("dafny-timeout-batch-kernel");

    let status = Command::new("dafny")
        .args(["build", "--target", "cs", "--no-verify", "--output"])
        .arg(&planner_path)
        .arg("proofs/dafny/executable/SchedulePlannerKernel.dfy")
        .status()
        .expect("failed to invoke dafny build for schedule planner kernel");

    if !status.success() {
        panic!("dafny build failed for schedule planner kernel");
    }

    println!(
        "cargo:rustc-env=RESONATE_DAFNY_SCHEDULE_PLANNER_DLL={}.dll",
        planner_path.display()
    );

    let status = Command::new("dafny")
        .args(["build", "--target", "cs", "--no-verify", "--output"])
        .arg(&runtime_kernel_path)
        .arg("proofs/dafny/executable/RuntimeStateKernel.dfy")
        .status()
        .expect("failed to invoke dafny build for runtime state kernel");

    if !status.success() {
        panic!("dafny build failed for runtime state kernel");
    }

    println!(
        "cargo:rustc-env=RESONATE_DAFNY_RUNTIME_KERNEL_DLL={}.dll",
        runtime_kernel_path.display()
    );

    let status = Command::new("dafny")
        .args(["build", "--target", "cs", "--no-verify", "--output"])
        .arg(&timeout_kernel_path)
        .arg("proofs/dafny/executable/TimeoutBatchKernel.dfy")
        .status()
        .expect("failed to invoke dafny build for timeout batch kernel");

    if !status.success() {
        panic!("dafny build failed for timeout batch kernel");
    }

    println!(
        "cargo:rustc-env=RESONATE_DAFNY_TIMEOUT_BATCH_KERNEL_DLL={}.dll",
        timeout_kernel_path.display()
    );
}
