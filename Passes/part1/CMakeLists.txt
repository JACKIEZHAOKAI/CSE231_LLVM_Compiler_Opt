add_llvm_library( submission_pt1 MODULE
  CountStaticInstructions.cpp
  CountDynamicInstructions.cpp
  
  PLUGIN_TOOL
  opt
  )