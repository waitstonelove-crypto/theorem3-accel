#!/usr/bin/env bash
# theorem3 项目构建脚本（复用共享 Mathlib 编译产物，无需重新编译 Mathlib）
# 用法：bash build.sh
# 共享 Mathlib：D:/AI/lean/mathlib（源码 + .lake 编译产物），依赖包在 mathlib/.lake/packages/ 下

set -e
export ELAN_HOME="D:/AI/lean/elan"
export LEAN="D:/AI/lean/elan/bin/lean.exe"
export LEAN_PATH="D:/AI/lean/projects/theorem3;D:/AI/lean/mathlib/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/Cli/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/batteries/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/Qq/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/aesop/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/proofwidgets/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/importGraph/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/LeanSearchClient/.lake/build/lib/lean;D:/AI/lean/mathlib/.lake/packages/plausible/.lake/build/lib/lean"

cd "$(dirname "$0")"
"$LEAN" -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false Core.lean -o Core.olean
"$LEAN" -DmaxSynthPendingDepth=3 -DrelaxedAutoImplicit=false Theorem3.lean -o Theorem3.olean
echo "build OK: Core.olean + Theorem3.olean（axiom 仅 1 个：lin_ode_input_convergence）"
