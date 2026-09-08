import LakeJs.Js

-- ============
-- Lean.Runtime
-- ============

-- ```lean
-- opaque closureMaxArgsFn : Unit → Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_closure_max_args(object *) {
--     return lean_unsigned_to_nat((unsigned)LEAN_CLOSURE_MAX_ARGS);
-- }
-- ```
def lean_closure_max_args := [JS_EXPR|throw new Error("lean_closure_max_args is not implemented")]

-- ```lean
-- opaque maxSmallNatFn : Unit → Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_max_small_nat(object *) {
--     return lean_usize_to_nat(LEAN_MAX_SMALL_NAT);
-- }
-- ```
def lean_max_small_nat := [JS_EXPR|throw new Error("lean_max_small_nat is not implemented")]

-- ```lean
-- opaque libUVVersionFn : Unit → Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
--     return lean_unsigned_to_nat(uv_version());
-- }
-- ```
def lean_libuv_version := [JS_EXPR|throw new Error("lean_libuv_version is not implemented")]

-- ```lean
-- opaque openSSLVersionFn : Unit → Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_openssl_version(lean_obj_arg o) {
--     return lean_unsigned_to_nat(OPENSSL_VERSION_NUMBER);
-- }
-- ```
def lean_openssl_version := [JS_EXPR|throw new Error("lean_openssl_version is not implemented")]

-- ============
-- Lean.Compiler.IR.LLVMBindings
-- ============

-- ```lean
-- opaque Value.getName {ctx : Context} (value : Value ctx) : BaseIO String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_value_name2 := [JS_EXPR|throw new Error("lean_llvm_get_value_name2 is not implemented")]

-- ```lean
-- opaque llvmInitializeTargetInfo : BaseIO (Unit)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_initialize_target_info := [JS_EXPR|throw new Error("lean_llvm_initialize_target_info is not implemented")]

-- ```lean
-- opaque createContext : BaseIO (Context)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_context := [JS_EXPR|throw new Error("lean_llvm_create_context is not implemented")]

-- ```lean
-- opaque createModule (ctx : Context) (name : @&String) : BaseIO (Module ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_module := [JS_EXPR|throw new Error("lean_llvm_create_module is not implemented")]

-- ```lean
-- opaque moduleToString (m : Module ctx) : BaseIO String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_module_to_string := [JS_EXPR|throw new Error("lean_llvm_module_to_string is not implemented")]

-- ```lean
-- opaque writeBitcodeToFile (m : Module ctx) (path : @&String) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_write_bitcode_to_file := [JS_EXPR|throw new Error("lean_llvm_write_bitcode_to_file is not implemented")]

-- ```lean
-- opaque addFunction (m : Module ctx) (name : @&String) (type : LLVMType ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_add_function := [JS_EXPR|throw new Error("lean_llvm_add_function is not implemented")]

-- ```lean
-- opaque getFirstFunction (m : Module ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_first_function := [JS_EXPR|throw new Error("lean_llvm_get_first_function is not implemented")]

-- ```lean
-- opaque getNextFunction (glbl : Value ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_next_function := [JS_EXPR|throw new Error("lean_llvm_get_next_function is not implemented")]

-- ```lean
-- opaque getNamedFunction (m : Module ctx) (name : @&String) : BaseIO (Option (Value ctx))
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_named_function := [JS_EXPR|throw new Error("lean_llvm_get_named_function is not implemented")]

-- ```lean
-- opaque addGlobal (m : Module ctx) (name : @&String) (type : LLVMType ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_add_global := [JS_EXPR|throw new Error("lean_llvm_add_global is not implemented")]

-- ```lean
-- opaque getNamedGlobal (m : Module ctx) (name : @&String) : BaseIO (Option (Value ctx))
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_named_global := [JS_EXPR|throw new Error("lean_llvm_get_named_global is not implemented")]

-- ```lean
-- opaque getFirstGlobal (m : Module ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_first_global := [JS_EXPR|throw new Error("lean_llvm_get_first_global is not implemented")]

-- ```lean
-- opaque getNextGlobal (glbl : Value ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_next_global := [JS_EXPR|throw new Error("lean_llvm_get_next_global is not implemented")]

-- ```lean
-- opaque buildGlobalString (builder : Builder ctx) (value : @&String) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_global_string := [JS_EXPR|throw new Error("lean_llvm_build_global_string is not implemented")]

-- ```lean
-- opaque isDeclaration (global : Value ctx) : BaseIO Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def llvm_is_declaration := [JS_EXPR|throw new Error("llvm_is_declaration is not implemented")]

-- ```lean
-- opaque setInitializer (glbl : Value ctx) (val : Value ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_set_initializer := [JS_EXPR|throw new Error("lean_llvm_set_initializer is not implemented")]

-- ```lean
-- opaque functionType (retty : LLVMType ctx) (args : @&Array (LLVMType ctx)) (isVarArg : Bool := false) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_function_type := [JS_EXPR|throw new Error("lean_llvm_function_type is not implemented")]

-- ```lean
-- opaque voidType (ctx : Context) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_void_type_in_context := [JS_EXPR|throw new Error("lean_llvm_void_type_in_context is not implemented")]

-- ```lean
-- opaque intTypeInContext (ctx : Context) (width : UInt64) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_int_type_in_context := [JS_EXPR|throw new Error("lean_llvm_int_type_in_context is not implemented")]

-- ```lean
-- opaque opaquePointerTypeInContext (ctx : Context) (addrspace: UInt64 := 0) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_opaque_pointer_type_in_context := [JS_EXPR|throw new Error("lean_llvm_opaque_pointer_type_in_context is not implemented")]

-- ```lean
-- opaque floatTypeInContext (ctx : Context) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_float_type_in_context := [JS_EXPR|throw new Error("lean_llvm_float_type_in_context is not implemented")]

-- ```lean
-- opaque doubleTypeInContext (ctx : Context) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_double_type_in_context := [JS_EXPR|throw new Error("lean_llvm_double_type_in_context is not implemented")]

-- ```lean
-- opaque pointerType (elemty : LLVMType ctx) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_pointer_type := [JS_EXPR|throw new Error("lean_llvm_pointer_type is not implemented")]

-- ```lean
-- opaque arrayType (elemty : LLVMType ctx) (nelem : UInt64) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_array_type := [JS_EXPR|throw new Error("lean_llvm_array_type is not implemented")]

-- ```lean
-- opaque constArray (elemty : LLVMType ctx) (vals : @&Array (Value ctx)) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_const_array := [JS_EXPR|throw new Error("lean_llvm_const_array is not implemented")]

-- ```lean
-- opaque constString (ctx : Context) (str : @&String) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_const_string := [JS_EXPR|throw new Error("lean_llvm_const_string is not implemented")]

-- ```lean
-- opaque constPointerNull (elemty : LLVMType ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_const_pointer_null := [JS_EXPR|throw new Error("lean_llvm_const_pointer_null is not implemented")]

-- ```lean
-- opaque getUndef (elemty : LLVMType ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_undef := [JS_EXPR|throw new Error("lean_llvm_get_undef is not implemented")]

-- ```lean
-- opaque createBuilderInContext (ctx : Context) : BaseIO (Builder ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_builder_in_context := [JS_EXPR|throw new Error("lean_llvm_create_builder_in_context is not implemented")]

-- ```lean
-- opaque appendBasicBlockInContext (ctx : Context) (fn :  Value ctx) (name :  @&String) : BaseIO (BasicBlock ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_append_basic_block_in_context := [JS_EXPR|throw new Error("lean_llvm_append_basic_block_in_context is not implemented")]

-- ```lean
-- opaque countBasicBlocks (fn : Value ctx) : BaseIO UInt64
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_count_basic_blocks := [JS_EXPR|throw new Error("lean_llvm_count_basic_blocks is not implemented")]

-- ```lean
-- opaque getEntryBasicBlock (fn : Value ctx) : BaseIO (BasicBlock ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_entry_basic_block := [JS_EXPR|throw new Error("lean_llvm_get_entry_basic_block is not implemented")]

-- ```lean
-- opaque getFirstInstruction (bb : BasicBlock ctx) : BaseIO (Option (Value ctx))
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_first_instruction := [JS_EXPR|throw new Error("lean_llvm_get_first_instruction is not implemented")]

-- ```lean
-- opaque positionBuilderBefore (builder : Builder ctx) (instr : Value ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_position_builder_before := [JS_EXPR|throw new Error("lean_llvm_position_builder_before is not implemented")]

-- ```lean
-- opaque positionBuilderAtEnd (builder : Builder ctx) (bb :  BasicBlock ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_position_builder_at_end := [JS_EXPR|throw new Error("lean_llvm_position_builder_at_end is not implemented")]

-- ```lean
-- opaque buildCall2 (builder : Builder ctx) (ty: LLVMType ctx) (fn : Value ctx) (args : @&Array (Value ctx)) (name :  @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_call2 := [JS_EXPR|throw new Error("lean_llvm_build_call2 is not implemented")]

-- ```lean
-- opaque setTailCall (fn : Value ctx) (istail : Bool) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_set_tail_call := [JS_EXPR|throw new Error("lean_llvm_set_tail_call is not implemented")]

-- ```lean
-- opaque buildCondBr (builder : Builder ctx) (if_ : Value ctx) (thenbb : BasicBlock ctx) (elsebb : BasicBlock ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_cond_br := [JS_EXPR|throw new Error("lean_llvm_build_cond_br is not implemented")]

-- ```lean
-- opaque buildBr (builder : Builder ctx) (bb : BasicBlock ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_br := [JS_EXPR|throw new Error("lean_llvm_build_br is not implemented")]

-- ```lean
-- opaque buildAlloca (builder : Builder ctx) (ty : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_alloca := [JS_EXPR|throw new Error("lean_llvm_build_alloca is not implemented")]

-- ```lean
-- opaque buildLoad2 (builder : Builder ctx) (ty: LLVMType ctx) (val : Value ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_load2 := [JS_EXPR|throw new Error("lean_llvm_build_load2 is not implemented")]

-- ```lean
-- opaque buildStore (builder : Builder ctx) (val : Value ctx) (store_loc_ptr : Value ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_store := [JS_EXPR|throw new Error("lean_llvm_build_store is not implemented")]

-- ```lean
-- opaque buildRet (builder : Builder ctx) (val : Value ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_ret := [JS_EXPR|throw new Error("lean_llvm_build_ret is not implemented")]

-- ```lean
-- opaque buildUnreachable (builder : Builder ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_unreachable := [JS_EXPR|throw new Error("lean_llvm_build_unreachable is not implemented")]

-- ```lean
-- opaque buildGEP2 (builder : Builder ctx) (ty: LLVMType ctx) (base : Value ctx) (ixs : @&Array (Value ctx)) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_gep2 := [JS_EXPR|throw new Error("lean_llvm_build_gep2 is not implemented")]

-- ```lean
-- opaque buildInBoundsGEP2 (builder : Builder ctx) (ty: LLVMType ctx) (base : Value ctx) (ixs : @&Array (Value ctx)) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_inbounds_gep2 := [JS_EXPR|throw new Error("lean_llvm_build_inbounds_gep2 is not implemented")]

-- ```lean
-- opaque buildSext (builder : Builder ctx) (val : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_sext := [JS_EXPR|throw new Error("lean_llvm_build_sext is not implemented")]

-- ```lean
-- opaque buildZext (builder : Builder ctx) (val : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_zext := [JS_EXPR|throw new Error("lean_llvm_build_zext is not implemented")]

-- ```lean
-- opaque buildSextOrTrunc (builder : Builder ctx) (val : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_sext_or_trunc := [JS_EXPR|throw new Error("lean_llvm_build_sext_or_trunc is not implemented")]

-- ```lean
-- opaque buildSwitch (builder : Builder ctx) (val : Value ctx) (elseBB : BasicBlock ctx) (numCasesHint : UInt64) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_switch := [JS_EXPR|throw new Error("lean_llvm_build_switch is not implemented")]

-- ```lean
-- opaque buildPtrToInt (builder : Builder ctx) (ptr : Value ctx) (destTy : LLVMType ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_ptr_to_int := [JS_EXPR|throw new Error("lean_llvm_build_ptr_to_int is not implemented")]

-- ```lean
-- opaque buildMul (builder : Builder ctx) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_mul := [JS_EXPR|throw new Error("lean_llvm_build_mul is not implemented")]

-- ```lean
-- opaque buildAdd (builder : Builder ctx) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_add := [JS_EXPR|throw new Error("lean_llvm_build_add is not implemented")]

-- ```lean
-- opaque buildSub (builder : Builder ctx) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_sub := [JS_EXPR|throw new Error("lean_llvm_build_sub is not implemented")]

-- ```lean
-- opaque buildNot (builder : Builder ctx) (x : Value ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_not := [JS_EXPR|throw new Error("lean_llvm_build_not is not implemented")]

-- ```lean
-- opaque buildICmp (builder : Builder ctx) (predicate : IntPredicate) (x y : Value ctx) (name : @&String := "") : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_build_icmp := [JS_EXPR|throw new Error("lean_llvm_build_icmp is not implemented")]

-- ```lean
-- opaque addCase (switch onVal : Value ctx) (destBB : BasicBlock ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_add_case := [JS_EXPR|throw new Error("lean_llvm_add_case is not implemented")]

-- ```lean
-- opaque getInsertBlock (builder : Builder ctx) : BaseIO (BasicBlock ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_insert_block := [JS_EXPR|throw new Error("lean_llvm_get_insert_block is not implemented")]

-- ```lean
-- opaque clearInsertionPosition (builder : Builder ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_clear_insertion_position := [JS_EXPR|throw new Error("lean_llvm_clear_insertion_position is not implemented")]

-- ```lean
-- opaque getBasicBlockParent (bb : BasicBlock ctx) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_basic_block_parent := [JS_EXPR|throw new Error("lean_llvm_get_basic_block_parent is not implemented")]

-- ```lean
-- opaque typeOf (val : Value ctx) : BaseIO (LLVMType ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_type_of := [JS_EXPR|throw new Error("lean_llvm_type_of is not implemented")]

-- ```lean
-- opaque constInt (intty : LLVMType ctx) (value : UInt64) (signExtend : @Bool := false) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_const_int := [JS_EXPR|throw new Error("lean_llvm_const_int is not implemented")]

-- ```lean
-- opaque printModuletoString (mod : Module ctx) : BaseIO (String)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_print_module_to_string := [JS_EXPR|throw new Error("lean_llvm_print_module_to_string is not implemented")]

-- ```lean
-- opaque printModuletoFile (mod : Module ctx) (file : @&String) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_print_module_to_file := [JS_EXPR|throw new Error("lean_llvm_print_module_to_file is not implemented")]

-- ```lean
-- opaque countParams (fn : Value ctx) : BaseIO UInt64
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def llvm_count_params := [JS_EXPR|throw new Error("llvm_count_params is not implemented")]

-- ```lean
-- opaque getParam (fn : Value ctx) (ix : UInt64) : BaseIO (Value ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def llvm_get_param := [JS_EXPR|throw new Error("llvm_get_param is not implemented")]

-- ```lean
-- opaque createMemoryBufferWithContentsOfFile (path : @&String) : BaseIO (MemoryBuffer ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_memory_buffer_with_contents_of_file := [JS_EXPR|throw new Error("lean_llvm_create_memory_buffer_with_contents_of_file is not implemented")]

-- ```lean
-- opaque parseBitcode (ctx : Context) (membuf : MemoryBuffer ctx) : BaseIO (Module ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_parse_bitcode := [JS_EXPR|throw new Error("lean_llvm_parse_bitcode is not implemented")]

-- ```lean
-- opaque linkModules (dest : Module ctx) (src : Module ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_link_modules := [JS_EXPR|throw new Error("lean_llvm_link_modules is not implemented")]

-- ```lean
-- opaque getDefaultTargetTriple : BaseIO String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_default_target_triple := [JS_EXPR|throw new Error("lean_llvm_get_default_target_triple is not implemented")]

-- ```lean
-- opaque getTargetFromTriple (triple : @&String) : BaseIO (Target ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_get_target_from_triple := [JS_EXPR|throw new Error("lean_llvm_get_target_from_triple is not implemented")]

-- ```lean
-- opaque createTargetMachine (target : Target ctx) (tripleStr : @&String) (cpu : @&String) (features : @&String) : BaseIO (TargetMachine ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_target_machine := [JS_EXPR|throw new Error("lean_llvm_create_target_machine is not implemented")]

-- ```lean
-- opaque targetMachineEmitToFile (targetMachine : TargetMachine ctx) (module : Module ctx) (filepath : @&String) (codegenType : LLVM.CodegenFileType) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_target_machine_emit_to_file := [JS_EXPR|throw new Error("lean_llvm_target_machine_emit_to_file is not implemented")]

-- ```lean
-- opaque createPassManager : BaseIO (PassManager ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_pass_manager := [JS_EXPR|throw new Error("lean_llvm_create_pass_manager is not implemented")]

-- ```lean
-- opaque disposePassManager (pm : PassManager ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_dispose_pass_manager := [JS_EXPR|throw new Error("lean_llvm_dispose_pass_manager is not implemented")]

-- ```lean
-- opaque runPassManager (pm : PassManager ctx) (mod : Module ctx): BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_run_pass_manager := [JS_EXPR|throw new Error("lean_llvm_run_pass_manager is not implemented")]

-- ```lean
-- opaque createPassManagerBuilder : BaseIO (PassManagerBuilder ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_pass_manager_builder := [JS_EXPR|throw new Error("lean_llvm_create_pass_manager_builder is not implemented")]

-- ```lean
-- opaque disposePassManagerBuilder (pmb : PassManagerBuilder ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_dispose_pass_manager_builder := [JS_EXPR|throw new Error("lean_llvm_dispose_pass_manager_builder is not implemented")]

-- ```lean
-- opaque PassManagerBuilder.setOptLevel (pmb : PassManagerBuilder ctx) (optLevel : unsigned) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_pass_manager_builder_set_opt_level := [JS_EXPR|throw new Error("lean_llvm_pass_manager_builder_set_opt_level is not implemented")]

-- ```lean
-- opaque PassManagerBuilder.populateModulePassManager (pmb : PassManagerBuilder ctx) (pm : PassManager ctx): BaseIO Unit
-- -/
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_pass_manager_builder_populate_module_pass_manager := [JS_EXPR|throw new Error("lean_llvm_pass_manager_builder_populate_module_pass_manager is not implemented")]

-- ```lean
-- opaque disposeTargetMachine (tm : TargetMachine ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_dispose_target_machine := [JS_EXPR|throw new Error("lean_llvm_dispose_target_machine is not implemented")]

-- ```lean
-- opaque disposeModule (m : Module ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_dispose_module := [JS_EXPR|throw new Error("lean_llvm_dispose_module is not implemented")]

-- ```lean
-- opaque verifyModule (m : Module ctx) : BaseIO (Option String)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_verify_module := [JS_EXPR|throw new Error("lean_llvm_verify_module is not implemented")]

-- ```lean
-- opaque createStringAttribute (key : String) (value : String) : BaseIO (Attribute ctx)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_create_string_attribute := [JS_EXPR|throw new Error("lean_llvm_create_string_attribute is not implemented")]

-- ```lean
-- opaque addAttributeAtIndex (fn : Value ctx) (idx: AttributeIndex) (attr: Attribute ctx) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_add_attribute_at_index := [JS_EXPR|throw new Error("lean_llvm_add_attribute_at_index is not implemented")]

-- ```lean
-- opaque setVisibility {ctx : Context} (value : Value ctx) (visibility : Visibility) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_set_visibility := [JS_EXPR|throw new Error("lean_llvm_set_visibility is not implemented")]

-- ```lean
-- opaque setDLLStorageClass {ctx : Context} (value : Value ctx) (dllStorageClass : DLLStorageClass) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_set_dll_storage_class := [JS_EXPR|throw new Error("lean_llvm_set_dll_storage_class is not implemented")]

-- ```lean
-- opaque setLinkage {ctx : Context} (value : Value ctx) (linkage : Linkage) : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_llvm_set_linkage := [JS_EXPR|throw new Error("lean_llvm_set_linkage is not implemented")]

-- ============
-- Lean.CompactedRegion
-- ============

-- ```lean
-- public unsafe opaque CompactedRegion.read {α : Type} (fname : @& System.FilePath)
--     (depRegions : @& Array CompactedRegion) : IO (α × CompactedRegion)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_compacted_region_read := [JS_EXPR|throw new Error("lean_compacted_region_read is not implemented")]

-- ============
-- Lean.Compiler.FFI
-- ============

-- ```lean
-- private opaque getLeancExtraFlags : Unit → String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_leanc_extra_flags := [JS_EXPR|throw new Error("lean_get_leanc_extra_flags is not implemented")]

-- ```lean
-- private opaque getLeancInternalFlags : Unit → String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_leanc_internal_flags := [JS_EXPR|throw new Error("lean_get_leanc_internal_flags is not implemented")]

-- ```lean
-- private opaque getBuiltinLinkerFlags (linkStatic : Bool) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_linker_flags := [JS_EXPR|throw new Error("lean_get_linker_flags is not implemented")]

-- ```lean
-- private opaque getBuiltinInternalLinkerFlags : Unit → String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_internal_linker_flags := [JS_EXPR|throw new Error("lean_get_internal_linker_flags is not implemented")]

-- ============
-- Lean.DocString.Links
-- ============

-- ```lean
-- private opaque getManualRoot : Unit → String
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_manual_get_root(lean_obj_arg _unit) {
--     return lean_mk_string(LEAN_MANUAL_ROOT);
-- }
-- ```
def lean_manual_get_root := [JS_EXPR|throw new Error("lean_manual_get_root is not implemented")]

-- ============
-- Lean.Util.Profile
-- ============

-- ```lean
-- def profileit {α : Type} (category : @& String) (opts : @& Options) (fn : Unit → α) (decl := Name.anonymous) : α := fn ()
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_profileit := [JS_EXPR|throw new Error("lean_profileit is not implemented")]

-- ```lean
-- opaque displayCumulativeProfilingTimes : BaseIO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_display_cumulative_profiling_times := [JS_EXPR|throw new Error("lean_display_cumulative_profiling_times is not implemented")]

-- ============
-- Lean.Level
-- ============

-- ```lean
-- opaque Level.mkData (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_level_mk_data (uint64_t h, object * depth, uint8_t hasMVar, uint8_t hasParam) {
--     if (!is_scalar(depth))
--         lean_internal_panic("universe level depth is too big");
--     size_t d = unbox(depth);
--     if (d > 16777215)
--         lean_internal_panic("universe level depth is too big");
--     uint32_t h1 = h;
--     return ((uint64_t) h1) + (((uint64_t) hasMVar) << 32) + (((uint64_t) hasParam) << 33) + (((uint64_t)d) << 40);
-- }
-- ```
def lean_level_mk_data := [JS_EXPR|throw new Error("lean_level_mk_data is not implemented")]

-- ```lean
-- protected opaque beq (a : @& Level) (b : @& Level) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_level_eq(object * l1, object * l2) {
--     return TO_REF(level, l1) == TO_REF(level, l2);
-- }
-- ```
def lean_level_eq := [JS_EXPR|throw new Error("lean_level_eq is not implemented")]

-- ============
-- Lean.Expr
-- ============

-- ```lean
-- def BinderInfo.toUInt64 : BinderInfo → UInt64
--   | .default        => 0
--   | .implicit       => 1
--   | .strictImplicit => 2
--   | .instImplicit   => 3
-- ```
--
-- ```cpp
-- static inline uint64_t lean_uint8_to_uint64(uint8_t a) { return ((uint64_t)a); }
-- ```
def lean_uint8_to_uint64 := [JS_EXPR|#0 & 0xFFFFFFFFFFFFFFFF]

-- ```lean
-- opaque Expr.mkData (h : UInt64) (looseBVarRange : Nat := 0) (approxDepth : UInt32 := 0)
--     (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false) : Expr.Data
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_expr_mk_data(uint64_t hash, object * bvarRange, uint32_t approxDepth, uint8_t hasFVar, uint8_t hasExprMVar, uint8_t hasLevelMVar, uint8_t hasLevelParam) {
--     if (approxDepth > 255) approxDepth = 255;
--     if (!is_scalar(bvarRange)) lean_internal_panic("too many bound variables");
--     size_t range = unbox(bvarRange);
--     if (range > 1048575) lean_internal_panic("too many bound variables");
--     uint32_t r = range;
--     uint32_t h = hash;
--     return ((uint64_t) h) + (((uint64_t) approxDepth) << 32) + (((uint64_t) hasFVar) << 40)
--     + (((uint64_t) hasExprMVar) << 41) + (((uint64_t) hasLevelMVar) << 42) + (((uint64_t) hasLevelParam) << 43)
--     + (((uint64_t) r) << 44);
-- }
-- ```
def lean_expr_mk_data := [JS_EXPR|throw new Error("lean_expr_mk_data is not implemented")]

-- ```lean
-- opaque Expr.mkAppData (fData : Data) (aData : Data) : Data
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint64_t lean_expr_mk_app_data(uint64_t fData, uint64_t aData) {
--   uint16_t depth = std::max(get_approx_depth(fData), get_approx_depth(aData)) + 1;
--   if (depth > 255) depth = 255;
--   uint32_t range = std::max(get_bvar_range(fData), get_bvar_range(aData));
--   uint32_t h = hash(fData, aData);
--   return ((fData | aData) & (((uint64_t) 15) << 40)) | ((uint64_t) h) | (((uint64_t) depth) << 32) | (((uint64_t) range) << 44);
-- }
-- ```
def lean_expr_mk_app_data := [JS_EXPR|throw new Error("lean_expr_mk_app_data is not implemented")]

-- ```lean
-- data : @& Expr → Data
--     | .const n lvls => mkData (mixHash 5 <| mixHash (hash n) (hash lvls)) 0 0 false false (lvls.any Level.hasMVar) (lvls.any Level.hasParam)
--     | .bvar idx => mkData (mixHash 7 <| hash idx) (idx+1)
--     | .sort lvl => mkData (mixHash 11 <| hash lvl) 0 0 false false lvl.hasMVar lvl.hasParam
--     | .fvar fvarId => mkData (mixHash 13 <| hash fvarId) 0 0 true
--     | .mvar fvarId => mkData (mixHash 17 <| hash fvarId) 0 0 false true
--     | .mdata _m e =>
--       let d := e.data.approxDepth.toUInt32+1
--       mkData (mixHash d.toUInt64 <| e.data.hash) e.data.looseBVarRange.toNat d e.data.hasFVar e.data.hasExprMVar e.data.hasLevelMVar e.data.hasLevelParam
--     | .proj s i e =>
--       let d := e.data.approxDepth.toUInt32+1
--       mkData (mixHash d.toUInt64 <| mixHash (hash s) <| mixHash (hash i) e.data.hash)
--           e.data.looseBVarRange.toNat d e.data.hasFVar e.data.hasExprMVar e.data.hasLevelMVar e.data.hasLevelParam
--     | .app f a => mkAppData f.data a.data
--     | .lam _ t b _ =>
--       let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
--       mkDataForBinder (mixHash d.toUInt64 <| mixHash t.data.hash b.data.hash)
--         (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1))
--         d
--         (t.data.hasFVar || b.data.hasFVar)
--         (t.data.hasExprMVar || b.data.hasExprMVar)
--         (t.data.hasLevelMVar || b.data.hasLevelMVar)
--         (t.data.hasLevelParam || b.data.hasLevelParam)
--     | .forallE _ t b _ =>
--       let d := (max t.data.approxDepth.toUInt32 b.data.approxDepth.toUInt32) + 1
--       mkDataForBinder (mixHash d.toUInt64 <| mixHash t.data.hash b.data.hash)
--         (max t.data.looseBVarRange.toNat (b.data.looseBVarRange.toNat - 1))
--         d
--         (t.data.hasFVar || b.data.hasFVar)
--         (t.data.hasExprMVar || b.data.hasExprMVar)
--         (t.data.hasLevelMVar || b.data.hasLevelMVar)
--         (t.data.hasLevelParam || b.data.hasLevelParam)
--     | .letE _ t v b _ =>
--       let d := (max (max t.data.approxDepth.toUInt32 v.data.approxDepth.toUInt32) b.data.approxDepth.toUInt32) + 1
--       mkDataForLet (mixHash d.toUInt64 <| mixHash t.data.hash <| mixHash v.data.hash b.data.hash)
--         (max (max t.data.looseBVarRange.toNat v.data.looseBVarRange.toNat) (b.data.looseBVarRange.toNat - 1))
--         d
--         (t.data.hasFVar || v.data.hasFVar || b.data.hasFVar)
--         (t.data.hasExprMVar || v.data.hasExprMVar || b.data.hasExprMVar)
--         (t.data.hasLevelMVar || v.data.hasLevelMVar || b.data.hasLevelMVar)
--         (t.data.hasLevelParam || v.data.hasLevelParam || b.data.hasLevelParam)
--     | .lit l => mkData (mixHash 3 (hash l))
-- ```
--
-- ```cpp
-- static inline uint64_t lean_expr_data(lean_obj_arg expr) {
--     return lean_ctor_get_uint64(expr, lean_ctor_num_objs(expr)*sizeof(void*));
-- }
-- ```
def lean_expr_data := [JS_EXPR|throw new Error("lean_expr_data is not implemented")]

-- ```lean
-- opaque dbgToString (e : @& Expr) : String
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_expr_dbg_to_string := [JS_EXPR|throw new Error("lean_expr_dbg_to_string is not implemented")]

-- ```lean
-- opaque quickLt (a : @& Expr) (b : @& Expr) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_expr_quick_lt := [JS_EXPR|throw new Error("lean_expr_quick_lt is not implemented")]

-- ```lean
-- opaque lt (a : @& Expr) (b : @& Expr) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_expr_lt := [JS_EXPR|throw new Error("lean_expr_lt is not implemented")]

-- ```lean
-- opaque eqv (a : @& Expr) (b : @& Expr) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_expr_eqv(b_obj_arg a, b_obj_arg b) {
--     return expr_eq_fn<false>()(TO_REF(expr, a), TO_REF(expr, b));
-- }
-- ```
def lean_expr_eqv := [JS_EXPR|throw new Error("lean_expr_eqv is not implemented")]

-- ```lean
-- opaque equal (a : @& Expr) (b : @& Expr) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_expr_equal(b_obj_arg a, b_obj_arg b) {
--     return expr_eq_fn<true>()(TO_REF(expr, a), TO_REF(expr, b));
-- }
-- ```
def lean_expr_equal := [JS_EXPR|throw new Error("lean_expr_equal is not implemented")]

-- ```lean
-- opaque hasLooseBVar (e : @& Expr) (bvarIdx : @& Nat) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_expr_has_loose_bvar(b_obj_arg e, b_obj_arg i) {
--     if (!lean_is_scalar(i))
--         return false;
--     return has_loose_bvar(TO_REF(expr, e), lean_unbox(i));
-- }
-- ```
def lean_expr_has_loose_bvar := [JS_EXPR|throw new Error("lean_expr_has_loose_bvar is not implemented")]

-- ```lean
-- opaque lowerLooseBVars (e : @& Expr) (s d : @& Nat) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_lower_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
--     if (!lean_is_scalar(s) || !lean_is_scalar(d) || lean_unbox(s) < lean_unbox(d)) {
--         lean_inc(e);
--         return e;
--     }
--     return lower_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
-- }
-- ```
def lean_expr_lower_loose_bvars := [JS_EXPR|throw new Error("lean_expr_lower_loose_bvars is not implemented")]

-- ```lean
-- opaque liftLooseBVars (e : @& Expr) (s d : @& Nat) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_lift_loose_bvars(b_obj_arg e, b_obj_arg s, b_obj_arg d) {
--     if (!lean_is_scalar(s) || !lean_is_scalar(d)) {
--         lean_inc(e);
--         return e;
--     }
--     return lift_loose_bvars(TO_REF(expr, e), lean_unbox(s), lean_unbox(d)).steal();
-- }
-- ```
def lean_expr_lift_loose_bvars := [JS_EXPR|throw new Error("lean_expr_lift_loose_bvars is not implemented")]

-- ```lean
-- opaque instantiate (e : @& Expr) (subst : @& Array Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_instantiate(b_obj_arg a, b_obj_arg subst) {
--     return lean_expr_instantiate_core(a, lean_array_size(subst), lean_array_cptr(subst));
-- }
-- ```
def lean_expr_instantiate := [JS_EXPR|throw new Error("lean_expr_instantiate is not implemented")]

-- ```lean
-- opaque instantiate1 (e : @& Expr) (subst : @& Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_instantiate1(object * a0, object * e0) {
--     expr const & a = reinterpret_cast<expr const &>(a0);
--     if (!has_loose_bvars(a)) {
--         lean_inc(a0);
--         return a0;
--     }
--     expr const & e = reinterpret_cast<expr const &>(e0);
--     expr r = instantiate(a, 1, &e);
--     return r.steal();
-- }
-- ```
def lean_expr_instantiate1 := [JS_EXPR|throw new Error("lean_expr_instantiate1 is not implemented")]

-- ```lean
-- opaque instantiateRev (e : @& Expr) (subst : @& Array Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_instantiate_rev(b_obj_arg a, b_obj_arg subst) {
--     return lean_expr_instantiate_rev_core(a, lean_array_size(subst), lean_array_cptr(subst));
-- }
-- ```
def lean_expr_instantiate_rev := [JS_EXPR|throw new Error("lean_expr_instantiate_rev is not implemented")]

-- ```lean
-- opaque instantiateRange (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_instantiate_range(b_obj_arg a, b_obj_arg begin, b_obj_arg end, b_obj_arg subst) {
--     if (!lean_is_scalar(begin) || !lean_is_scalar(end)) {
--         lean_internal_panic("invalid range for Expr.instantiateRange");
--     } else {
--         usize sz = lean_array_size(subst);
--         usize b  = lean_unbox(begin);
--         usize e  = lean_unbox(end);
--         if (b > e || e > sz) {
--             lean_internal_panic("invalid range for Expr.instantiateRange");
--         }
--         return lean_expr_instantiate_core(a, e - b, lean_array_cptr(subst) + b);
--     }
-- }
-- ```
def lean_expr_instantiate_range := [JS_EXPR|throw new Error("lean_expr_instantiate_range is not implemented")]

-- ```lean
-- opaque instantiateRevRange (e : @& Expr) (beginIdx endIdx : @& Nat) (subst : @& Array Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_instantiate_rev_range(b_obj_arg a, b_obj_arg begin, b_obj_arg end, b_obj_arg subst) {
--     if (!lean_is_scalar(begin) || !lean_is_scalar(end)) {
--         lean_internal_panic("invalid range for Expr.instantiateRevRange");
--     } else {
--         usize sz = lean_array_size(subst);
--         usize b  = lean_unbox(begin);
--         usize e  = lean_unbox(end);
--         if (b > e || e > sz) {
--             lean_internal_panic("invalid range for Expr.instantiateRevRange");
--         }
--         return lean_expr_instantiate_rev_core(a, e - b, lean_array_cptr(subst) + b);
--     }
-- }
-- ```
def lean_expr_instantiate_rev_range := [JS_EXPR|throw new Error("lean_expr_instantiate_rev_range is not implemented")]

-- ```lean
-- opaque abstract (e : @& Expr) (xs : @& Array Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_abstract(object * e, object * subst) {
--     return lean_expr_abstract_core(e, lean_array_size(subst), subst);
-- }
-- ```
def lean_expr_abstract := [JS_EXPR|throw new Error("lean_expr_abstract is not implemented")]

-- ```lean
-- opaque abstractRange (e : @& Expr) (n : @& Nat) (xs : @& Array Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_expr_abstract_range(object * e, object * n, object * subst) {
--     if (!lean_is_scalar(n))
--         return lean_expr_abstract_core(e, lean_array_size(subst), subst);
--     else
--         return lean_expr_abstract_core(e, std::min(lean_unbox(n), lean_array_size(subst)), subst);
-- }
-- ```
def lean_expr_abstract_range := [JS_EXPR|throw new Error("lean_expr_abstract_range is not implemented")]

-- ============
-- Lean.Util.FindExpr
-- ============

-- ```lean
-- opaque findImpl? (p : @& (Expr → Bool)) (e : @& Expr) : Option Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_find_expr(b_obj_arg p, b_obj_arg e_) {
--     lean_object * found = nullptr;
--     expr const & e = TO_REF(expr, e_);
--     for_each_fn<true>([&](expr const & e) {
--         if (found != nullptr) return false;
--         lean_inc(p);
--         lean_inc(e.raw());
--         if (lean_unbox(lean_apply_1(p, e.raw()))) {
--             found = e.raw();
--             return false;
--         }
--         return true;
--     })(e);
--     if (found) {
--         lean_inc(found);
--         lean_object * r = lean_alloc_ctor(1, 1, 0);
--         lean_ctor_set(r, 0, found);
--         return r;
--     } else {
--         return lean_box(0);
--     }
-- }
-- ```
def lean_find_expr := [JS_EXPR|throw new Error("lean_find_expr is not implemented")]

-- ```lean
-- opaque findExtImpl? (p : @& (Expr → FindStep)) (e : @& Expr) : Option Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_find_ext_expr(b_obj_arg p, b_obj_arg e_) {
--     lean_object * found = nullptr;
--     expr const & e = TO_REF(expr, e_);
--     // Recall that `findExt?` skips partial applications.
--     for_each_fn<false>([&](expr const & e) {
--         if (found != nullptr) return false;
--         lean_inc(p);
--         lean_inc(e.raw());
--         switch(lean_unbox(lean_apply_1(p, e.raw()))) {
--         case 0: // found
--             found = e.raw();
--             return false;
--         case 1: // visit
--             return true;
--         case 2: // done
--             return false;
--         default:
--             lean_unreachable();
--         }
--     })(e);
--     if (found) {
--         lean_inc(found);
--         lean_object * r = lean_alloc_ctor(1, 1, 0);
--         lean_ctor_set(r, 0, found);
--         return r;
--     } else {
--         return lean_box(0);
--     }
-- }
-- ```
def lean_find_ext_expr := [JS_EXPR|throw new Error("lean_find_ext_expr is not implemented")]

-- ============
-- Lean.Util.ReplaceExpr
-- ============

-- ```lean
-- opaque replaceImpl (f? : @& (Expr → Option Expr)) (e : @& Expr) : Expr
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_replace_expr(b_obj_arg f, b_obj_arg e) {
--     expr r = replace_fn(f)(TO_REF(expr, e));
--     return r.steal();
-- }
-- ```
def lean_replace_expr := [JS_EXPR|throw new Error("lean_replace_expr is not implemented")]

-- ============
-- Lean.MetavarContext
-- ============

-- ```lean
-- opaque instantiateLevelMVarsImp (mctx : MetavarContext) (l : Level) : MetavarContext × Level
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_instantiate_level_mvars := [JS_EXPR|throw new Error("lean_instantiate_level_mvars is not implemented")]

-- ```lean
-- opaque instantiateExprMVarsImp (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_instantiate_expr_mvars := [JS_EXPR|throw new Error("lean_instantiate_expr_mvars is not implemented")]

-- ============
-- Lean.LoadDynlib
-- ============

-- ```lean
-- opaque Dynlib.load (path : @& System.FilePath) : IO Dynlib
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_dynlib_load := [JS_EXPR|throw new Error("lean_dynlib_load is not implemented")]

-- ```lean
-- opaque Dynlib.get? (dynlib : @& Dynlib) (sym : @& String) : Option dynlib.Symbol
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_dynlib_get := [JS_EXPR|throw new Error("lean_dynlib_get is not implemented")]

-- ```lean
-- unsafe opaque Dynlib.Symbol.runAsInit {dynlib : @& Dynlib} (sym : @& dynlib.Symbol) : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_dynlib_symbol_run_as_init := [JS_EXPR|throw new Error("lean_dynlib_symbol_run_as_init is not implemented")]

-- ============
-- Lean.Setup
-- ============

-- ```lean
-- opaque Idbg.idbgClientLoop {α : Type} [Nonempty α]
--   (siteId : String) (imports : Array Import) (apply : α → String) : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_idbg_client_loop := [JS_EXPR|throw new Error("lean_idbg_client_loop is not implemented")]

-- ============
-- Lean.Environment
-- ============

-- ```lean
-- opaque addDeclCore (env : Environment) (maxHeartbeats : USize) (maxRecDepth : USize)
--   (decl : @& Declaration) (cancelTk? : @& Option IO.CancelToken) : Except Exception Environment
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT object * lean_add_decl(object * env, size_t max_heartbeat, size_t max_rec_depth,
--     object * decl, object * opt_cancel_tk) {
--     scope_max_heartbeat s(max_heartbeat);
--     scope_max_rec_depth s2(max_rec_depth);
--     scope_cancel_tk s3(is_scalar(opt_cancel_tk) ? nullptr : cnstr_get(opt_cancel_tk, 0));
--     return catch_kernel_exceptions<environment>([&]() {
--             return environment(env).add(declaration(decl, true));
--         });
-- }
-- ```
def lean_add_decl := [JS_EXPR|throw new Error("lean_add_decl is not implemented")]

-- ```lean
-- private opaque addDeclCheck (env : Environment) (maxHeartbeats : USize) (maxRecDepth : USize)
--   (decl : @& Declaration) (cancelTk? : @& Option IO.CancelToken) : Except Kernel.Exception Environment
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_elab_add_decl := [JS_EXPR|throw new Error("lean_elab_add_decl is not implemented")]

-- ```lean
-- private opaque addDeclWithoutChecking (env : Environment) (decl : @& Declaration) :
--   Except Kernel.Exception Environment
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_elab_add_decl_without_checking := [JS_EXPR|throw new Error("lean_elab_add_decl_without_checking is not implemented")]

-- ```lean
-- private opaque isReservedName (env : Environment) (name : Name) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_is_reserved_name := [JS_EXPR|throw new Error("lean_is_reserved_name is not implemented")]

-- ```lean
-- private opaque getIRExtraConstNames (env : Environment) (level : OLeanLevel) (includeDecls := false) : Array Name
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_ir_extra_const_names := [JS_EXPR|throw new Error("lean_get_ir_extra_const_names is not implemented")]

-- ```lean
-- private opaque exportIREntries (env : Environment) : Array (Name × Array EnvExtensionEntry)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_ir_export_entries := [JS_EXPR|throw new Error("lean_ir_export_entries is not implemented")]

-- ```lean
-- opaque updateEnvAttributes : Environment → IO Environment
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_update_env_attributes := [JS_EXPR|throw new Error("lean_update_env_attributes is not implemented")]

-- ```lean
-- opaque getNumBuiltinAttributes : IO Nat
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_num_attributes := [JS_EXPR|throw new Error("lean_get_num_attributes is not implemented")]

-- ```lean
-- private opaque runInitAttrs (env : Environment) (opts : Options) : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_run_init_attrs := [JS_EXPR|throw new Error("lean_run_init_attrs is not implemented")]

-- ```lean
-- private unsafe opaque evalConstCore (α) (env : @& Environment) (opts : @& Options) (constName : @& Name) : Except String α
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_eval_const := [JS_EXPR|throw new Error("lean_eval_const is not implemented")]

-- ```lean
-- private opaque evalCheckMeta (env : Environment) (constName : Name) : Except String Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_eval_check_meta := [JS_EXPR|throw new Error("lean_eval_check_meta is not implemented")]

-- ```lean
-- opaque isDefEq (env : Lean.Environment) (lctx : LocalContext) (a b : Expr) : Except Kernel.Exception Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_kernel_is_def_eq := [JS_EXPR|throw new Error("lean_kernel_is_def_eq is not implemented")]

-- ```lean
-- opaque whnf (env : Lean.Environment) (lctx : LocalContext) (a : Expr) : Except Kernel.Exception Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_kernel_whnf := [JS_EXPR|throw new Error("lean_kernel_whnf is not implemented")]

-- ```lean
-- opaque check (env : Lean.Environment) (lctx : LocalContext) (a : Expr) : Except Kernel.Exception Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_kernel_check := [JS_EXPR|throw new Error("lean_kernel_check is not implemented")]

-- ============
-- Lean.MonadEnv
-- ============

-- ```lean
-- opaque hasCompileError (env : Environment) (constName : Name) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_has_compile_error := [JS_EXPR|throw new Error("lean_has_compile_error is not implemented")]

-- ============
-- Lean.Compiler.ExternAttr
-- ============

-- ```lean
-- `
--    encoding: ```.entries = [standard `all "levelHash"]```
-- - `@[extern cpp "lean::string_size" llvm "lean_str_size"]`
--    encoding: ```.entries = [standard `cpp "lean::string_size", standard `llvm "leanStrSize"]```
-- - `@[extern cpp inline "#1 + #2"]`
--    encoding: ```.entries = [inline `cpp "#1 + #2"]```
-- - `@[extern cpp "foo" llvm adhoc]`
--    encoding: ```.entries = [standard `cpp "foo", adhoc `llvm]```
-- -/
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def level_hash := [JS_EXPR|throw new Error("level_hash is not implemented")]

-- ============
-- Lean.Meta.Basic
-- ============

-- ```lean
-- opaque whnf : Expr → MetaM Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_whnf := [JS_EXPR|throw new Error("lean_whnf is not implemented")]

-- ```lean
-- opaque inferType : Expr → MetaM Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_infer_type := [JS_EXPR|throw new Error("lean_infer_type is not implemented")]

-- ```lean
-- opaque isExprDefEqAux : Expr → Expr → MetaM Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_is_expr_def_eq := [JS_EXPR|throw new Error("lean_is_expr_def_eq is not implemented")]

-- ```lean
-- opaque isLevelDefEqAux : Level → Level → MetaM Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_is_level_def_eq := [JS_EXPR|throw new Error("lean_is_level_def_eq is not implemented")]

-- ```lean
-- protected opaque synthPending : MVarId → MetaM Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_synth_pending := [JS_EXPR|throw new Error("lean_synth_pending is not implemented")]

-- ```lean
-- opaque _root_.Lean.MVarId.checkedAssign (mvarId : MVarId) (val : Expr) : MetaM Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_checked_assign := [JS_EXPR|throw new Error("lean_checked_assign is not implemented")]

-- ============
-- Lean.Meta.WHNF
-- ============

-- ```lean
-- opaque getStructuralRecArgPos? (declName : Name) : CoreM (Option Nat)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_structural_rec_arg_pos := [JS_EXPR|throw new Error("lean_get_structural_rec_arg_pos is not implemented")]

-- ============
-- Lean.Compiler.InitAttr
-- ============

-- ```lean
-- private unsafe opaque runModInitCore (sym : @& String) : IO Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_run_mod_init_core := [JS_EXPR|throw new Error("lean_run_mod_init_core is not implemented")]

-- ```lean
-- unsafe opaque runInit (env : @& Environment) (opts : @& Options) (decl initDecl : @& Name) : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_run_init := [JS_EXPR|throw new Error("lean_run_init is not implemented")]

-- ============
-- Lean.Meta.Sym.DSimp.DSimpM
-- ============

-- ```lean
-- -- Forward declaration
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_sym_dsimp := [JS_EXPR|throw new Error("lean_sym_dsimp is not implemented")]

-- ============
-- Lean.Meta.Constructions.CasesOn
-- ============

-- ```lean
-- opaque mkCasesOnImp (env : Kernel.Environment) (declName : @& Name) : Except Kernel.Exception Declaration
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_mk_cases_on := [JS_EXPR|throw new Error("lean_mk_cases_on is not implemented")]

-- ============
-- Lean.Meta.Match.MatchEqsExt
-- ============

-- ```lean
-- opaque getEquationsFor (matchDeclName : Name) : MetaM MatchEqns
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_match_equations_for := [JS_EXPR|throw new Error("lean_get_match_equations_for is not implemented")]

-- ```lean
-- opaque genMatchCongrEqns (matchDeclName : Name) : MetaM (Array Name)
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_get_congr_match_equations_for := [JS_EXPR|throw new Error("lean_get_congr_match_equations_for is not implemented")]

-- ============
-- Lean.Meta.Sym.Pattern
-- ============

-- ```lean
-- -- Forward definition
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_sym_def_eq := [JS_EXPR|throw new Error("lean_sym_def_eq is not implemented")]

-- ============
-- Lean.Meta.Sym.Simp.SimpM
-- ============

-- ```lean
-- -- Forward declaration
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_sym_simp := [JS_EXPR|throw new Error("lean_sym_simp is not implemented")]

-- ============
-- Lean.PrettyPrinter.Formatter
-- ============

-- ```lean
-- opaque mkAntiquot.formatter' (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Formatter
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_mk_antiquot_formatter := [JS_EXPR|throw new Error("lean_mk_antiquot_formatter is not implemented")]

-- ```lean
-- opaque interpretParserDescr' : ParserDescr → CoreM Formatter
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_pretty_printer_formatter_interpret_parser_descr := [JS_EXPR|throw new Error("lean_pretty_printer_formatter_interpret_parser_descr is not implemented")]

-- ============
-- Lean.PrettyPrinter.Parenthesizer
-- ============

-- ```lean
-- opaque mkAntiquot.parenthesizer' (name : String) (kind : SyntaxNodeKind) (anonymous := true) (isPseudoKind := false) : Parenthesizer
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_mk_antiquot_parenthesizer := [JS_EXPR|throw new Error("lean_mk_antiquot_parenthesizer is not implemented")]

-- ```lean
-- opaque interpretParserDescr' : ParserDescr → CoreM Parenthesizer
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_pretty_printer_parenthesizer_interpret_parser_descr := [JS_EXPR|throw new Error("lean_pretty_printer_parenthesizer_interpret_parser_descr is not implemented")]

-- ============
-- Lean.Meta.Tactic.Simp.Types
-- ============

-- ```lean
-- opaque simp (e : Expr) : SimpM Result
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_simp := [JS_EXPR|throw new Error("lean_simp is not implemented")]

-- ```lean
-- opaque dsimp (e : Expr) : SimpM Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_dsimp := [JS_EXPR|throw new Error("lean_dsimp is not implemented")]

-- ============
-- Lean.Meta.Tactic.Grind.Util
-- ============

-- ```lean
-- -- forward definition
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_normalize := [JS_EXPR|throw new Error("lean_grind_normalize is not implemented")]

-- ============
-- Lean.Compiler.IR.Checker
-- ============

-- ```lean
-- opaque getMaxCtorFields : Unit → Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_get_max_ctor_fields(lean_obj_arg _unit) {
--     return lean_box(LEAN_MAX_CTOR_FIELDS);
-- }
-- ```
def lean_get_max_ctor_fields := [JS_EXPR|throw new Error("lean_get_max_ctor_fields is not implemented")]

-- ```lean
-- opaque getMaxCtorScalarsSize : Unit → Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_get_max_ctor_scalars_size(lean_obj_arg _unit) {
--     return lean_box(LEAN_MAX_CTOR_SCALARS_SIZE);
-- }
-- ```
def lean_get_max_ctor_scalars_size := [JS_EXPR|throw new Error("lean_get_max_ctor_scalars_size is not implemented")]

-- ```lean
-- opaque getMaxCtorTag : Unit → Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_get_max_ctor_tag(lean_obj_arg _unit) {
--     return lean_box(LeanMaxCtorTag);
-- }
-- ```
def lean_get_max_ctor_tag := [JS_EXPR|throw new Error("lean_get_max_ctor_tag is not implemented")]

-- ```lean
-- opaque getUSizeSize : Unit → Nat
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_get_usize_size(lean_obj_arg _unit) {
--     return lean_box(sizeof(size_t));
-- }
-- ```
def lean_get_usize_size := [JS_EXPR|throw new Error("lean_get_usize_size is not implemented")]

-- ============
-- Lean.Meta.Match.Match
-- ============

-- ```lean
-- def neg (n : @& Int) : Int :=
--        match n with
--        | ofNat n   => negOfNat n
--        | negSucc n => succ n
--        ```
--        which is defined **before** `Int.decLt` -/
--     let (matcher, addMatcher) ← mkMatcherAuxDefinition matcherName type val (isSplitter := input.isSplitter.isSome)
--     trace[Meta.Match.debug] "matcher levels: {matcher.getAppFn.constLevels!}, uElim: {uElimGen}"
--     let uElimPos? ← getUElimPos? matcher.getAppFn.constLevels! uElimGen
--     discard <| isLevelDefEq uElimGen uElim
--     let addMatcher :=
--       match addMatcher with
--       | some addMatcher => addMatcher <|
--         { numParams := matcher.getAppNumArgs
--           altInfos
--           discrInfos
--           numDiscrs
--           uElimPos?
--           overlaps := s.overlaps
--           }
--       | none => pure ()
-- 
--     trace[Meta.Match.debug] "matcher: {matcher}"
--     let unusedAltIdxs := lhss.length.fold (init := []) fun i _ r =>
--       if s.used.contains i then r else i::r
--     return {
--       matcher,
--       counterExamples := s.counterExamples,
--       unusedAltIdxs := unusedAltIdxs.reverse,
--       addMatcher
--     }
-- 
--   let motiveType ← mkForallFVars discrs (mkSort uElimGen)
--   trace[Meta.Match.debug] "motiveType: {motiveType}"
--   withLocalDeclD `motive motiveType fun motive => do
--   if discrInfos.any fun info => info.hName?.isSome then
--     forallBoundedTelescope matchType numDiscrs fun discrs' _ => do
--     let (mvarType, isEqMask) ← withEqs discrs discrs' discrInfos fun eqs => do
--       let mvarType ← mkForallFVars eqs (mkAppN motive discrs')
--       let isEqMask ← eqs.mapM fun eq => return (← inferType eq).isEq
--       return (mvarType, isEqMask)
--     trace[Meta.Match.debug] "target: {mvarType}"
--     withAlts motive discrs discrInfos lhss isSplitter fun alts minors altInfos => do
--       let mvar ← mkFreshExprMVar mvarType
--       trace[Meta.Match.debug] "goal\n{mvar.mvarId!}"
--       let examples := discrs'.toList.map fun discr => Example.var discr.fvarId!
--       let (_, s) ← (process { mvarId := mvar.mvarId!, vars := discrs'.toList, alts := alts, examples := examples }).run {}
--       let val ← mkLambdaFVars discrs' mvar
--       trace[Meta.Match.debug] "matcher\nvalue: {val}\ntype: {← inferType val}"
--       let mut rfls := #[]
--       let mut isEqMaskIdx := 0
--       for discr in discrs, info in discrInfos do
--         if info.hName?.isSome then
--           if isEqMask[isEqMaskIdx]! then
--             rfls := rfls.push (← mkEqRefl discr)
--           else
--             rfls := rfls.push (← mkHEqRefl discr)
--           isEqMaskIdx := isEqMaskIdx + 1
--       let val := mkAppN (mkAppN val discrs) rfls
--       let args := #[motive] ++ discrs ++ minors
--       let val ← mkLambdaFVars args val
--       let type ← mkForallFVars args (mkAppN motive discrs)
--       mkMatcher type val altInfos s
--   else
--     let mvarType  := mkAppN motive discrs
--     trace[Meta.Match.debug] "target: {mvarType}"
--     withAlts motive discrs discrInfos lhss isSplitter fun alts minors altInfos => do
--       let mvar ← mkFreshExprMVar mvarType
--       let examples := discrs.toList.map fun discr => Example.var discr.fvarId!
--       let (_, s) ← (process { mvarId := mvar.mvarId!, vars := discrs.toList, alts := alts, examples := examples }).run {}
--       let args := #[motive] ++ discrs ++ minors
--       let type ← mkForallFVars args mvarType
--       let val  ← mkLambdaFVars args mvar
--       mkMatcher type val altInfos s
-- ```
--
-- ```cpp
-- static inline lean_obj_res lean_int_neg(b_lean_obj_arg a) {
--     if (LEAN_LIKELY(lean_is_scalar(a))) {
--         return lean_int64_to_int(-lean_scalar_to_int64(a));
--     } else {
--         return lean_int_big_neg(a);
--     }
-- }
-- ```
def lean_int_neg := [JS_EXPR|-#0]

-- ============
-- Lean.Linter.UnusedVariables
-- ============

-- ```lean
-- def foo (unused : Nat) : Nat := ...`
-- * `@[implemented_by bla] def foo (unused : Nat) : Nat := ...`
-- -/
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def bla := [JS_EXPR|throw new Error("bla is not implemented")]

-- ============
-- Lean.Meta.Tactic.Grind.Types
-- ============

-- ```lean
-- opaque mkEqProof (a b : Expr) : GoalM Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_mk_eq_proof := [JS_EXPR|throw new Error("lean_grind_mk_eq_proof is not implemented")]

-- ```lean
-- opaque mkHEqProof (a b : Expr) : GoalM Expr
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_mk_heq_proof := [JS_EXPR|throw new Error("lean_grind_mk_heq_proof is not implemented")]

-- ```lean
-- opaque processNewFacts : GoalM Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_process_new_facts := [JS_EXPR|throw new Error("lean_grind_process_new_facts is not implemented")]

-- ```lean
-- opaque internalize (e : Expr) (generation : Nat) (parent? : Option Expr := none) : GoalM Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_internalize := [JS_EXPR|throw new Error("lean_grind_internalize is not implemented")]

-- ```lean
-- opaque preprocess : Expr → GoalM Simp.Result
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_preprocess := [JS_EXPR|throw new Error("lean_grind_preprocess is not implemented")]

-- ============
-- Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
-- ============

-- ```lean
-- -- forward definition
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_cutsat_mk_var := [JS_EXPR|throw new Error("lean_grind_cutsat_mk_var is not implemented")]

-- ```lean
-- -- forward definition
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_cutsat_assert_eq := [JS_EXPR|throw new Error("lean_grind_cutsat_assert_eq is not implemented")]

-- ```lean
-- -- forward definition
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_grind_cutsat_assert_le := [JS_EXPR|throw new Error("lean_grind_cutsat_assert_le is not implemented")]

-- ============
-- Lean.Meta.Tactic.Grind.Arith.Cutsat.Var
-- ============

-- ```lean
-- opaque propagateNonlinearTerm (y : Var) (x : Var) : GoalM Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_cutsat_propagate_nonlinear := [JS_EXPR|throw new Error("lean_cutsat_propagate_nonlinear is not implemented")]

-- ============
-- Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof
-- ============

-- ```lean
-- -- forward definition
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_cutsat_eq_cnstr_to_proof := [JS_EXPR|throw new Error("lean_cutsat_eq_cnstr_to_proof is not implemented")]

-- ============
-- Lean.Elab.Tactic.Try
-- ============

-- ```lean
-- -- forward definition to avoid mutual block
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_eval_suggest_tactic := [JS_EXPR|throw new Error("lean_eval_suggest_tactic is not implemented")]

-- ============
-- Lean.Shell
-- ============

-- ```lean
-- opaque decodeLossyUTF8 (a : @& ByteArray) : String
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_decode_lossy_utf8(b_obj_arg a) {
--     return lean_mk_string_from_bytes(reinterpret_cast<char *>(lean_sarray_cptr(a)), lean_sarray_size(a));
-- }
-- ```
def lean_decode_lossy_utf8 := [JS_EXPR|throw new Error("lean_decode_lossy_utf8 is not implemented")]

-- ```lean
-- opaque runMain (env : @& Environment) (opts : @& Options) (args : @& List String) : BaseIO UInt32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_eval_main := [JS_EXPR|throw new Error("lean_eval_main is not implemented")]

-- ```lean
-- opaque initLLVM : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_init_llvm := [JS_EXPR|throw new Error("lean_init_llvm is not implemented")]

-- ```lean
-- opaque emitLLVM (env : Environment) (modName : Name) (filepath : FilePath) : IO Unit
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_emit_llvm := [JS_EXPR|throw new Error("lean_emit_llvm is not implemented")]

-- ```lean
-- opaque Internal.hasAddressSanitizer (_ : Unit) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_internal_has_address_sanitizer(obj_arg) {
-- #if defined(__has_feature)
-- #if __has_feature(address_sanitizer)
--     return 1;
-- #else
--     return 0;
-- #endif
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_internal_has_address_sanitizer := [JS_EXPR|throw new Error("lean_internal_has_address_sanitizer is not implemented")]

-- ```lean
-- opaque Internal.isMultiThread (_ : Unit) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_internal_is_multi_thread(obj_arg) {
-- #ifdef LEAN_MULTI_THREAD
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_internal_is_multi_thread := [JS_EXPR|throw new Error("lean_internal_is_multi_thread is not implemented")]

-- ```lean
-- opaque Internal.isDebug (_ : Unit) : Bool
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT uint8 lean_internal_is_debug(obj_arg) {
-- #ifdef LEAN_DEBUG
--     return 1;
-- #else
--     return 0;
-- #endif
-- }
-- ```
def lean_internal_is_debug := [JS_EXPR|throw new Error("lean_internal_is_debug is not implemented")]

-- ```lean
-- opaque Internal.getBuildType (_ : Unit) : String
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_internal_get_build_type(obj_arg) {
--     return mk_string(LEAN_STR(LEAN_BUILD_TYPE));
-- }
-- ```
def lean_internal_get_build_type := [JS_EXPR|throw new Error("lean_internal_get_build_type is not implemented")]

-- ```lean
-- opaque Internal.getDefaultMaxMemory (_ : Unit) : Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_internal_get_default_max_memory() {
-- #ifdef LEAN_DEFAULT_MAX_MEMORY
--     return lean_box(LEAN_DEFAULT_MAX_MEMORY);
-- #else
--     return lean_box(0);
-- #endif
-- }
-- ```
def lean_internal_get_default_max_memory := [JS_EXPR|throw new Error("lean_internal_get_default_max_memory is not implemented")]

-- ```lean
-- opaque Internal.setMaxMemory (max : USize) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_internal_set_max_memory(size_t max) {
--     set_max_memory(max);
--     return lean_box(0);
-- }
-- ```
def lean_internal_set_max_memory := [JS_EXPR|throw new Error("lean_internal_set_max_memory is not implemented")]

-- ```lean
-- opaque Internal.getDefaultMaxHeartbeat (_ : Unit) : Nat
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_internal_get_default_max_heartbeat() {
-- #ifdef LEAN_DEFAULT_MAX_HEARTBEAT
--     return lean_box(LEAN_DEFAULT_MAX_HEARTBEAT);
-- #else
--     return lean_box(0);
-- #endif
-- }
-- ```
def lean_internal_get_default_max_heartbeat := [JS_EXPR|throw new Error("lean_internal_get_default_max_heartbeat is not implemented")]

-- ```lean
-- opaque Internal.setMaxHeartbeat (max : USize) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_internal_set_max_heartbeat(usize max) {
--     set_max_heartbeat(max);
--     return lean_box(0);
-- }
-- ```
def lean_internal_set_max_heartbeat := [JS_EXPR|throw new Error("lean_internal_set_max_heartbeat is not implemented")]

-- ```lean
-- opaque Internal.getDefaultVerbose (_ : Unit) : Bool
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_internal_get_default_verbose := [JS_EXPR|throw new Error("lean_internal_get_default_verbose is not implemented")]

-- ```lean
-- opaque Internal.setExitOnPanic (exit : Bool) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT obj_res lean_internal_set_exit_on_panic(uint8 exit) {
--     g_exit_on_panic = exit;
--     return box(0);
-- }
-- ```
def lean_internal_set_exit_on_panic := [JS_EXPR|throw new Error("lean_internal_set_exit_on_panic is not implemented")]

-- ```lean
-- opaque Internal.setThreadStackSize (sz : USize) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_internal_set_thread_stack_size(size_t sz) {
--     lthread::set_thread_stack_size(sz);
--     return lean_box(0);
-- }
-- ```
def lean_internal_set_thread_stack_size := [JS_EXPR|throw new Error("lean_internal_set_thread_stack_size is not implemented")]

-- ```lean
-- opaque Internal.enableDebug (tag : @& String) : BaseIO Unit
-- ```
--
-- ```cpp
-- extern "C" LEAN_EXPORT lean_obj_res lean_internal_enable_debug(b_lean_obj_arg tag) {
--     enable_debug(lean_string_cstr(tag));
--     return lean_box(0);
-- }
-- ```
def lean_internal_enable_debug := [JS_EXPR|throw new Error("lean_internal_enable_debug is not implemented")]

-- ```lean
-- opaque Internal.getOptionOverrides (_ : Unit) : Options
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_internal_get_option_overrides := [JS_EXPR|throw new Error("lean_internal_get_option_overrides is not implemented")]

-- ```lean
-- opaque Internal.getBelieverTrustLevel (_ : Unit) : UInt32
-- ```
--
-- ```cpp
-- // (no C++ implementation found)
-- ```
def lean_internal_get_believer_trust_level := [JS_EXPR|throw new Error("lean_internal_get_believer_trust_level is not implemented")]
