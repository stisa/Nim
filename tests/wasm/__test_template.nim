discard """
  cmd:      "nim wasm -r $options $file"
  matrix:   "--gc:arc; --gc:arc --d:release"
  targets:  "wasm"
  action:   "run"
  exitcode: 0
  timeout:  60.0
"""