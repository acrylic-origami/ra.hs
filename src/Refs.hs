module Ra.Refs (
  write_funs,
  read_funs
) where
  write_funs = [
    "atomicallyWriteIORef", "writeIORef", "modifyIORef", "atomicallyModifyIORef", "atomicallyModifyIORef'",
    "putMVar", "swapMVar", "tryPutMVar", "modifyMVar", "modifyMVar_", "modifyMVarMasked_", "modifyMVarMasked",
    "writeTVar", "modifyTVar", "modifyTVar'", "stateTVar", "swapTVar",
    "writeSTRef", "modifySTRef", "modifySTRef'"
  ]
  read_funs = [
    "readIORef", "modifyIORef", "atomicallyModifyIORef", "atomicallyModifyIORef'",
    "readMVar", "tryReadMVar", "isEmptyMVar", "swapMVar", "modifyMVar", "modifyMVar_", "modifyMVarMasked_", "modifyMVarMasked", "withMVar", "withMVarMasked",
    "readTVar", "modifyTVar", "modifyTVar'", "stateTVar", "swapTVar"
    "readSTRef", "modifySTRef", "modifySTRef'"
  ]