add_llvm_library( submission_pt1 MODULE
  CountStaticInstructions.cpp

  PLUGIN_TOOL
  opt
  )