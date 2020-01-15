add_llvm_library( LLVMTestPass MODULE
  TestPass.cpp

  PLUGIN_TOOL
  opt
  )
