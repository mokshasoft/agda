# Makefile for Once formal verification (Agda proofs)
#
# PREREQUISITE: Run from within 'nix develop' shell (from repo root).
# The standard library path is discovered dynamically from the Nix environment.
#
# Usage:
#   make              - Type-check all proofs
#   make compiler     - Type-check all compiler proofs (frontend + all backends)
#   make frontend     - Type-check frontend only (no backends)
#
#   Architecture-specific:
#   make x86-compiler    - Type-check x86-64 compiler (frontend + x86 backends)
#   make x86v3-compiler  - Type-check X86v3 SlotMachine compiler (POC)
#   make aarch64-compiler - Type-check AArch64 compiler (frontend + AArch64 backends)
#   make riscv-compiler  - Type-check RISC-V compiler (frontend + RISC-V backends)
#
#   CCC backends (categorical combinator code generators):
#   make ccc          - Type-check all CCC backends
#   make x86-ccc      - Type-check x86-64 CCC backend (whole-program proofs)
#   make x86v3-ccc    - Type-check X86v3 SlotMachine CCC backend (POC)
#   make aarch64-ccc  - Type-check AArch64 CCC backend
#   make riscv-ccc    - Type-check RISC-V CCC backend
#
#   Arithmetic backends:
#   make x86-arith    - Type-check x86-64 arithmetic backend
#   make aarch64-arith - Type-check AArch64 arithmetic backend
#   make riscv-arith  - Type-check RISC-V arithmetic backend
#   make arith        - Type-check all arithmetic backends
#
#   Other targets:
#   make clean        - Remove Agda build artifacts
#   make count-postulates - Count postulates by file (all architectures)
#   make count-postulates-x86 - Count postulates for x86-64 compiler only
#   make count-postulates-riscv - Count postulates for RISC-V compiler only
#   make count-postulates-arm - Count postulates for AArch64 compiler only
#   make agda MODULE=path - Type-check a single module

# Main entry points for each module
POSTULATES := Once/Postulates.agda
LAWS := Once/Category/Laws.agda
SOUNDNESS := Once/TypeSystem/Soundness.agda
ELABORATE := Once/Surface/Elaborate.agda
CORRECT := Once/Surface/Correct.agda
SURFACE_IR := Once/Surface/IR.agda
SURFACE_DESUGAR := Once/Surface/Desugar.agda
SURFACE_DESUGAR_CORRECT := Once/Surface/Desugar/Correct.agda
COMPILE := Once/Compile.agda
OPTIMIZE := Once/Optimize.agda
OPTIMIZE_CORRECT := Once/Optimize/Correct.agda
X86_SYNTAX := Once/Backend/X86/Syntax.agda
X86_SEMANTICS := Once/Backend/X86/Semantics.agda
X86_CODEGEN := Once/Backend/X86/CodeGen.agda
X86_CORRECT := Once/Backend/X86/Correct.agda
X86_STAR := Once/Backend/X86/Correct/Star.agda
X86_STARBASE := Once/Backend/X86/Correct/StarBase.agda
X86_WHOLEPROGRAM := Once/Backend/X86/Correct/WholeProgram.agda
X86_ENCODING := Once/Backend/X86/Encoding.agda
X86V3_DISPATCHER := Once/Backend/X86v3/Dispatcher.agda
AARCH64_SYNTAX := Once/Backend/AArch64/Syntax.agda
AARCH64_SEMANTICS := Once/Backend/AArch64/Semantics.agda
AARCH64_CODEGEN := Once/Backend/AArch64/CodeGen.agda
AARCH64_CORRECT := Once/Backend/AArch64/Correct.agda
AARCH64_FOUNDATION := Once/Backend/AArch64/Correct/Foundation.agda
RISCV_SYNTAX := Once/Backend/RiscV64/Syntax.agda
RISCV_SEMANTICS := Once/Backend/RiscV64/Semantics.agda
RISCV_CODEGEN := Once/Backend/RiscV64/CodeGen.agda
RISCV_CORRECT := Once/Backend/RiscV64/Correct.agda
RISCV_FOUNDATION := Once/Backend/RiscV64/Correct/Foundation.agda
COMMON_FETCH := Once/Backend/Common/Fetch.agda
COMMON_EXEC := Once/Backend/Common/Exec.agda
COMMON_MEMORY := Once/Backend/Common/Memory.agda
AARCH64_EMIT := Once/Backend/AArch64/Emit.agda
X86_EMIT := Once/Backend/X86/Emit.agda
RISCV_EMIT := Once/Backend/RiscV64/Emit.agda
EMIT_ALL := Once/Backend/Emit.agda
SPF := Once/SPF.agda
TERMINATION := Once/Backend/Termination.agda

# Arithmetic compiler (OCP-0001)
ARITH_TYPE := Once/Arith/Type.agda
ARITH_IR := Once/Arith/IR.agda
ARITH_SEMANTICS := Once/Arith/Semantics.agda
ARITH_X86_SYNTAX := Once/Arith/Backend/X86/Syntax.agda
ARITH_X86_CODEGEN := Once/Arith/Backend/X86/CodeGen.agda
ARITH_X86_CORRECT := Once/Arith/Backend/X86/Correct.agda
ARITH_AARCH64_SYNTAX := Once/Arith/Backend/AArch64/Syntax.agda
ARITH_AARCH64_CODEGEN := Once/Arith/Backend/AArch64/CodeGen.agda
ARITH_AARCH64_CORRECT := Once/Arith/Backend/AArch64/Correct.agda
ARITH_RISCV_SYNTAX := Once/Arith/Backend/RiscV/Syntax.agda
ARITH_RISCV_CODEGEN := Once/Arith/Backend/RiscV/CodeGen.agda
ARITH_RISCV_CORRECT := Once/Arith/Backend/RiscV/Correct.agda
ARITH_BOUNDARY := Once/Arith/Boundary.agda
ARITH_EMIT := Once/Arith/Backend/Emit.agda

# Verified type checker (OCP-0003)
TYPECHECK_RAW := Once/TypeCheck/Raw.agda
TYPECHECK_CONTEXT := Once/TypeCheck/Context.agda
TYPECHECK_ERROR := Once/TypeCheck/Error.agda
TYPECHECK_UNIFY := Once/TypeCheck/Unify.agda
TYPECHECK_RESOLVE := Once/TypeCheck/Resolve.agda
TYPECHECK_ELABORATE := Once/TypeCheck/Elaborate.agda
TYPECHECK_MAIN := Once/TypeCheck.agda

# Agda command: discovers standard library path from Nix store
# The library file is created dynamically to avoid hardcoded paths
define AGDA_CMD
STD_LIB=$$(find /nix/store -maxdepth 2 -name "standard-library.agda-lib" 2>/dev/null | head -1); \
if [ -z "$$STD_LIB" ]; then echo "Error: standard-library not found in Nix store"; exit 1; fi; \
unset AGDA_DIR; agda --library-file=<(echo "$$STD_LIB"; echo "Once.agda-lib")
endef

.PHONY: all
all: check

.PHONY: check
check: compiler spf
	@echo "All proofs type-check successfully!"

.PHONY: frontend
frontend: postulates laws surface surfaceir optimize
	@echo "Frontend proofs type-check successfully!"

.PHONY: postulates
postulates:
	@echo "Type-checking postulates..."
	@sh -c '$(AGDA_CMD) $(POSTULATES)'

.PHONY: laws
laws:
	@echo "Type-checking categorical laws..."
	@sh -c '$(AGDA_CMD) $(LAWS)'
	@sh -c '$(AGDA_CMD) $(SOUNDNESS)'

.PHONY: surface
surface:
	@echo "Type-checking surface syntax elaboration..."
	@sh -c '$(AGDA_CMD) $(ELABORATE)'
	@sh -c '$(AGDA_CMD) $(CORRECT)'

.PHONY: surfaceir
surfaceir:
	@echo "Type-checking surface IR and desugar..."
	@sh -c '$(AGDA_CMD) $(SURFACE_IR)'
	@sh -c '$(AGDA_CMD) $(SURFACE_DESUGAR)'
	@sh -c '$(AGDA_CMD) $(SURFACE_DESUGAR_CORRECT)'

.PHONY: optimize
optimize:
	@echo "Type-checking optimizer..."
	@sh -c '$(AGDA_CMD) $(OPTIMIZE)'
	@sh -c '$(AGDA_CMD) $(OPTIMIZE_CORRECT)'

.PHONY: common
common:
	@echo "Type-checking common backend lemmas..."
	@sh -c '$(AGDA_CMD) $(COMMON_FETCH)'
	@sh -c '$(AGDA_CMD) $(COMMON_EXEC)'
	@sh -c '$(AGDA_CMD) $(COMMON_MEMORY)'

.PHONY: x86-ccc
x86-ccc:
	@echo "Type-checking x86-64 CCC backend (whole-program)..."
	@sh -c '$(AGDA_CMD) $(X86_SYNTAX)'
	@sh -c '$(AGDA_CMD) $(X86_SEMANTICS)'
	@sh -c '$(AGDA_CMD) $(X86_CODEGEN)'
	@sh -c '$(AGDA_CMD) $(X86_WHOLEPROGRAM)'

.PHONY: x86v3-ccc
x86v3-ccc:
	@echo "Type-checking X86v3 SlotMachine CCC backend (POC)..."
	@sh -c '$(AGDA_CMD) $(X86V3_DISPATCHER)'

.PHONY: x86-star
x86-star:
	@echo "Type-checking x86-64 star relation module..."
	@sh -c '$(AGDA_CMD) $(X86_STAR)'

.PHONY: x86-starbase
x86-starbase:
	@echo "Type-checking x86-64 star base proofs..."
	@sh -c '$(AGDA_CMD) $(X86_STARBASE)'

.PHONY: x86-encoding
x86-encoding:
	@echo "Type-checking x86-64 encoding derivations..."
	@sh -c '$(AGDA_CMD) $(X86_ENCODING)'

.PHONY: aarch64-ccc
aarch64-ccc:
	@echo "Type-checking AArch64 CCC backend..."
	@sh -c '$(AGDA_CMD) $(AARCH64_SYNTAX)'
	@sh -c '$(AGDA_CMD) $(AARCH64_SEMANTICS)'
	@sh -c '$(AGDA_CMD) $(AARCH64_CODEGEN)'
	@sh -c '$(AGDA_CMD) $(AARCH64_CORRECT)'

.PHONY: aarch64-ccc-correct
aarch64-ccc-correct:
	@echo "Type-checking AArch64 CCC correctness proofs only..."
	@sh -c '$(AGDA_CMD) $(AARCH64_CORRECT)'

.PHONY: aarch64-foundation
aarch64-foundation:
	@echo "Type-checking AArch64 foundation module only..."
	@sh -c '$(AGDA_CMD) $(AARCH64_FOUNDATION)'

.PHONY: riscv-ccc
riscv-ccc:
	@echo "Type-checking RISC-V 64-bit CCC backend..."
	@sh -c '$(AGDA_CMD) $(RISCV_SYNTAX)'
	@if [ -f "$(RISCV_SEMANTICS)" ]; then sh -c '$(AGDA_CMD) $(RISCV_SEMANTICS)'; fi
	@if [ -f "$(RISCV_CODEGEN)" ]; then sh -c '$(AGDA_CMD) $(RISCV_CODEGEN)'; fi
	@if [ -f "$(RISCV_CORRECT)" ]; then sh -c '$(AGDA_CMD) $(RISCV_CORRECT)'; fi

.PHONY: riscv-ccc-correct
riscv-ccc-correct:
	@echo "Type-checking RISC-V CCC correctness proofs only..."
	@if [ -f "$(RISCV_CORRECT)" ]; then sh -c '$(AGDA_CMD) $(RISCV_CORRECT)'; fi

.PHONY: ccc
ccc: x86-ccc x86v3-ccc aarch64-ccc riscv-ccc
	@echo "All CCC backends type-check successfully!"

.PHONY: riscv-foundation
riscv-foundation:
	@echo "Type-checking RISC-V foundation module only..."
	@sh -c '$(AGDA_CMD) $(RISCV_FOUNDATION)'

.PHONY: termination
termination:
	@echo "Type-checking termination proof (orthogonal IR termination)..."
	@sh -c '$(AGDA_CMD) $(TERMINATION)'

.PHONY: spf
spf:
	@echo "Type-checking strictly positive functors..."
	@sh -c '$(AGDA_CMD) $(SPF)'

.PHONY: arith-core
arith-core:
	@echo "Type-checking arithmetic core (Type, IR, Semantics, Boundary)..."
	@sh -c '$(AGDA_CMD) $(ARITH_TYPE)'
	@sh -c '$(AGDA_CMD) $(ARITH_IR)'
	@sh -c '$(AGDA_CMD) $(ARITH_SEMANTICS)'
	@sh -c '$(AGDA_CMD) $(ARITH_BOUNDARY)'

.PHONY: x86-arith
x86-arith: arith-core
	@echo "Type-checking x86-64 arithmetic backend..."
	@sh -c '$(AGDA_CMD) $(ARITH_X86_SYNTAX)'
	@sh -c '$(AGDA_CMD) $(ARITH_X86_CODEGEN)'
	@sh -c '$(AGDA_CMD) $(ARITH_X86_CORRECT)'

.PHONY: aarch64-arith
aarch64-arith: arith-core
	@echo "Type-checking AArch64 arithmetic backend..."
	@sh -c '$(AGDA_CMD) $(ARITH_AARCH64_SYNTAX)'
	@sh -c '$(AGDA_CMD) $(ARITH_AARCH64_CODEGEN)'
	@sh -c '$(AGDA_CMD) $(ARITH_AARCH64_CORRECT)'

.PHONY: riscv-arith
riscv-arith: arith-core
	@echo "Type-checking RISC-V arithmetic backend..."
	@sh -c '$(AGDA_CMD) $(ARITH_RISCV_SYNTAX)'
	@sh -c '$(AGDA_CMD) $(ARITH_RISCV_CODEGEN)'
	@sh -c '$(AGDA_CMD) $(ARITH_RISCV_CORRECT)'

.PHONY: arith
arith: x86-arith aarch64-arith riscv-arith
	@echo "All arithmetic proofs type-check successfully!"

# Architecture-specific compiler targets (frontend + common + arch backends)
.PHONY: x86-compiler
x86-compiler: frontend common x86-ccc x86-arith
	@echo "x86-64 compiler proofs type-check successfully!"

.PHONY: aarch64-compiler
aarch64-compiler: frontend common aarch64-ccc aarch64-arith
	@echo "AArch64 compiler proofs type-check successfully!"

.PHONY: riscv-compiler
riscv-compiler: frontend common riscv-ccc riscv-arith
	@echo "RISC-V compiler proofs type-check successfully!"

.PHONY: x86v3-compiler
x86v3-compiler: frontend common x86v3-ccc
	@echo "X86v3 SlotMachine compiler proofs type-check successfully!"

# All compiler proofs
.PHONY: compiler
compiler: frontend common x86-ccc aarch64-ccc riscv-ccc arith
	@echo "All compiler proofs type-check successfully!"

.PHONY: malonzo
malonzo:
	@echo "Extracting entire compiler via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(COMPILE)'
	@echo "Copying extracted modules to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Surface
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Optimize
	@# Copy main compilation entry point
	@cp _build/malonzo/MAlonzo/Code/Once/Compile.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@# Copy core IR modules
	@cp _build/malonzo/MAlonzo/Code/Once/Type.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/IR.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Semantics.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@# Copy Surface IR and desugar
	@cp -r _build/malonzo/MAlonzo/Code/Once/Surface/* ../compiler/src/MAlonzo/Code/Once/Surface/ 2>/dev/null || true
	@# Copy optimizer
	@cp _build/malonzo/MAlonzo/Code/Once/Optimize.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp -r _build/malonzo/MAlonzo/Code/Once/Optimize/* ../compiler/src/MAlonzo/Code/Once/Optimize/ 2>/dev/null || true
	@echo "Done! Entire compiler extracted to compiler/src/MAlonzo/Code/Once/"
	@echo "Entry point: MAlonzo.Code.Once.Compile.compile"

.PHONY: emit
emit:
	@echo "Type-checking assembly emission modules..."
	@sh -c '$(AGDA_CMD) $(AARCH64_EMIT)'
	@sh -c '$(AGDA_CMD) $(X86_EMIT)'
	@sh -c '$(AGDA_CMD) $(RISCV_EMIT)'
	@sh -c '$(AGDA_CMD) $(EMIT_ALL)'

.PHONY: malonzo-codegen
malonzo-codegen:
	@echo "Extracting verified code generators via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(EMIT_ALL)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Backend
	@cp -r _build/malonzo/MAlonzo/Code/Once/Backend/* ../compiler/src/MAlonzo/Code/Once/Backend/
	@echo "  - Backend modules copied"
	@# Copy core dependencies (IR, Type) that Backend modules need
	@cp _build/malonzo/MAlonzo/Code/Once/IR.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Type.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@echo "  - Core IR/Type modules copied"
	@echo "Done. Verified code generators in compiler/src/MAlonzo/Code/Once/Backend/"

.PHONY: malonzo-arith
malonzo-arith:
	@echo "Extracting verified arithmetic backends via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(ARITH_EMIT)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Arith/Backend/X86
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Arith/Backend/AArch64
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Arith/Backend/RiscV
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/X86/*.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/X86/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/AArch64/*.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/AArch64/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/RiscV/*.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/RiscV/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/Emit.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/ 2>/dev/null || true
	@# Copy dependencies
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Type.hs ../compiler/src/MAlonzo/Code/Once/Arith/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/IR.hs ../compiler/src/MAlonzo/Code/Once/Arith/ 2>/dev/null || true
	@echo "Done. Verified arithmetic backends in compiler/src/MAlonzo/Code/Once/Arith/Backend/"

.PHONY: malonzo-arith-codegen
malonzo-arith-codegen:
	@echo "Extracting verified arithmetic code generators via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(ARITH_X86_CODEGEN)'
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(ARITH_AARCH64_CODEGEN)'
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(ARITH_RISCV_CODEGEN)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Arith/Backend/X86
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Arith/Backend/AArch64
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Arith/Backend/RiscV
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/X86/*.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/X86/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/AArch64/*.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/AArch64/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Backend/RiscV/*.hs ../compiler/src/MAlonzo/Code/Once/Arith/Backend/RiscV/ 2>/dev/null || true
	@# Copy IR and dependencies
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Type.hs ../compiler/src/MAlonzo/Code/Once/Arith/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/IR.hs ../compiler/src/MAlonzo/Code/Once/Arith/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Arith/Semantics.hs ../compiler/src/MAlonzo/Code/Once/Arith/ 2>/dev/null || true
	@echo "Done. Verified code generators in compiler/src/MAlonzo/Code/Once/Arith/Backend/"

# Verified type checker (OCP-0003)
.PHONY: typecheck-verified
typecheck-verified:
	@echo "Type-checking verified type checker (OCP-0003)..."
	@sh -c '$(AGDA_CMD) $(TYPECHECK_RAW)'
	@sh -c '$(AGDA_CMD) $(TYPECHECK_CONTEXT)'
	@sh -c '$(AGDA_CMD) $(TYPECHECK_ERROR)'

# Core type checker modules (unification only, inference is in Elaborate)
.PHONY: typecheck-core
typecheck-core: typecheck-verified
	@sh -c '$(AGDA_CMD) $(TYPECHECK_UNIFY)'
	@echo "Core type checker type-checks successfully!"

# Full type checker with scope resolution and extraction entry point
.PHONY: typecheck-full
typecheck-full: typecheck-core
	@sh -c '$(AGDA_CMD) $(TYPECHECK_RESOLVE)'
	@sh -c '$(AGDA_CMD) $(TYPECHECK_MAIN)'
	@echo "Verified type checker type-checks successfully!"

# Fast target for checking just the Elaborate module (for quick iteration)
.PHONY: typecheck-elaborate
typecheck-elaborate:
	@echo "Type-checking TypeCheck.Elaborate module..."
	@sh -c '$(AGDA_CMD) $(TYPECHECK_ELABORATE)'
	@echo "TypeCheck.Elaborate type-checks successfully!"

.PHONY: malonzo-typecheck
malonzo-typecheck:
	@echo "Extracting verified type checker via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(TYPECHECK_MAIN)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/TypeCheck
	@cp -r _build/malonzo/MAlonzo/Code/Once/TypeCheck/* ../compiler/src/MAlonzo/Code/Once/TypeCheck/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/TypeCheck.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@echo "Done. Verified type checker in compiler/src/MAlonzo/Code/Once/TypeCheck/"

.PHONY: malonzo-elaborate
malonzo-elaborate:
	@echo "Extracting Surface.Elaborate via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo $(ELABORATE)'
	@echo "Copying MAlonzo files to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once/Surface
	@cp -r _build/malonzo/MAlonzo/Code/Once/Surface/* ../compiler/src/MAlonzo/Code/Once/Surface/ 2>/dev/null || true
	@echo "Done. Surface.Elaborate in compiler/src/MAlonzo/Code/Once/Surface/"

.PHONY: malonzo-core
malonzo-core:
	@echo "Extracting core modules (Type, IR, Semantics, Memory, Postulates) via MAlonzo..."
	@mkdir -p _build/malonzo
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Type.agda'
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/IR.agda'
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Semantics.agda'
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Memory.agda'
	@sh -c '$(AGDA_CMD) -c --ghc-dont-call-ghc --compile-dir=_build/malonzo Once/Postulates.agda'
	@echo "Copying core modules to compiler..."
	@mkdir -p ../compiler/src/MAlonzo/Code/Once
	@cp _build/malonzo/MAlonzo/Code/Once/Type.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/IR.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Semantics.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Memory.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@cp _build/malonzo/MAlonzo/Code/Once/Postulates.hs ../compiler/src/MAlonzo/Code/Once/ 2>/dev/null || true
	@echo "Done. Core modules in compiler/src/MAlonzo/Code/Once/"

# Awk script to count postulates (handles multiple patterns)
# Pattern 1: Postulate block (postulate alone on line, followed by indented signatures)
# Pattern 2: Inline postulate (postulate name : Type on same line)
define AWK_POSTULATES
/^[[:space:]]*postulate[[:space:]]*$$/ { \
	in_postulate = 1; \
	match($$0, /^[[:space:]]*/); \
	post_indent = RLENGTH; \
	next \
} \
in_postulate && /[^[:space:]]/ { \
	match($$0, /^[[:space:]]*/); \
	if (RLENGTH <= post_indent) { in_postulate = 0 } \
} \
in_postulate && /^[[:space:]]+[^[:space:]:]+[[:space:]]*:/ { print } \
/^[[:space:]]*postulate[[:space:]]+[^[:space:]:]+[[:space:]]*:/ { \
	sub(/^[[:space:]]*postulate[[:space:]]+/, ""); \
	print \
}
endef
export AWK_POSTULATES

# Helper for postulate counting with optional architecture filtering
define COUNT_POSTULATES
	@echo "Counting postulates in $(DESC)..."
	@echo "(Counts type signatures within postulate blocks, including indented ones)"
	@echo ""
	@echo "=== Postulates by File ==="
	@find . -name "*.agda" -type f $(FILTER) | sort | while read f; do \
		postulates=$$(awk "$$AWK_POSTULATES" "$$f"); \
		if [ -n "$$postulates" ]; then \
			count=$$(echo "$$postulates" | wc -l | tr -d ' '); \
			echo ""; \
			echo "--- $$f ($$count) ---"; \
			echo "$$postulates" | sed 's/^[[:space:]]*/  /'; \
		fi; \
	done
	@echo ""
	@echo "=== Summary ==="
	@TOTAL=$$(find . -name "*.agda" -type f $(FILTER) | while read f; do \
		awk "$$AWK_POSTULATES" "$$f"; \
	done | wc -l | tr -d ' '); \
	FILES=$$(find . -name "*.agda" -type f $(FILTER) | while read f; do \
		count=$$(awk "$$AWK_POSTULATES" "$$f" | wc -l | tr -d ' '); \
		if [ "$$count" -gt 0 ]; then echo "$$f"; fi; \
	done | wc -l | tr -d ' '); \
	echo "Total postulates$(LABEL): $$TOTAL"; \
	echo "Files with postulates: $$FILES"
endef

.PHONY: count-postulates
count-postulates:
	$(eval DESC=Once compiler proof postulates)
	$(eval FILTER=)
	$(eval LABEL=)
	$(COUNT_POSTULATES)

.PHONY: count-postulates-x86
count-postulates-x86:
	$(eval DESC=Once x86-64 compiler (shared + x86-specific))
	$(eval FILTER=| grep -Ev "AArch64|RiscV64|RiscV")
	$(eval LABEL= (x86-64))
	$(COUNT_POSTULATES)

.PHONY: count-postulates-x86v3
count-postulates-x86v3:
	$(eval DESC=X86v3 SlotMachine POC (SlotMachine + X86v3))
	$(eval FILTER=| grep -E "X86v3")
	$(eval LABEL= (X86v3 POC))
	$(COUNT_POSTULATES)

.PHONY: count-postulates-riscv
count-postulates-riscv:
	$(eval DESC=Once RISC-V compiler (shared + RISC-V-specific))
	$(eval FILTER=| grep -Ev "X86|AArch64")
	$(eval LABEL= (RISC-V))
	$(COUNT_POSTULATES)

.PHONY: count-postulates-arm
count-postulates-arm:
	$(eval DESC=Once AArch64 compiler (shared + AArch64-specific))
	$(eval FILTER=| grep -Ev "X86|RiscV64|RiscV")
	$(eval LABEL= (AArch64))
	$(COUNT_POSTULATES)

.PHONY: clean
clean:
	rm -rf _build
	find . -name "*.agdai" -delete

# Type-check a single Agda module
# Usage: make agda MODULE=Once/Path/To/File.agda
.PHONY: agda
agda:
	@if [ -z "$(MODULE)" ]; then echo "Usage: make agda MODULE=Once/Path/To/File.agda"; exit 1; fi
	@echo "Type-checking $(MODULE)..."
	@sh -c '$(AGDA_CMD) $(MODULE)'
