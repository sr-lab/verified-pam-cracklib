{-# LANGUAGE ForeignFunctionInterface #-}
 
module PamInterface where
 
import Foreign.C.Types
import Foreign.C.String
import Foreign.Ptr (nullPtr)

import Data.Maybe (catMaybes)

-- Import functional code that was extracted from Coq
import PasswordPolicyGenerated

-- Main check (depends on process_checkers)
main_check_hs :: CString -> CString -> IO CString
main_check_hs oldPwd newPwd = 
 do
    if (oldPwd /= nullPtr) then
     do
      o <- peekCString oldPwd 
      n <- peekCString newPwd
      let s = concatMap (\s -> '\n':s) $ process_checkers pwd_quality_policy (Just o) n
      newCString s
    else
     do
      n <- peekCString newPwd
      let s = concatMap (\s -> '\n':s) $ process_checkers pwd_quality_policy Nothing n
      newCString s

foreign export ccall main_check_hs :: CString -> CString -> IO CString

-- Run password checkers, one by one (collecting error messages)
process_checkers :: [PasswordTransition -> Maybe ErrorMsg] -> Maybe Password -> Password -> [ErrorMsg]
process_checkers []     _      _       = []
process_checkers (c:cs) oldPwd newPwd  = (catMaybes [c (PwdTransition oldPwd newPwd)]) ++ process_checkers cs oldPwd newPwd
