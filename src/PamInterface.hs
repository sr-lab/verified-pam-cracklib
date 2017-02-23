{-# LANGUAGE ForeignFunctionInterface #-}
 
module PamInterface where
 
import Foreign.C.Types
import Foreign.C.String

-- Unsure about this one
import System.IO.Unsafe

-- Import functional code that can be generated
import PamGenerated

-- TODO: can I get rid of the unsafePerformIO?
palindrome_hs :: CString -> CInt
palindrome_hs = fromIntegral . bool_to_nat . palindrome . unsafePerformIO . peekCString

minclass_hs :: CString -> CInt -> CInt
minclass_hs s m = (fromIntegral (bool_to_nat (minclass (unsafePerformIO (peekCString s)) (fromIntegral m))))
 
wordcheck_hs :: CString -> CString -> CInt
wordcheck_hs h n = (fromIntegral (bool_to_nat (wordcheck (unsafePerformIO (peekCString h)) (unsafePerformIO (peekCString n)))))
 
foreign export ccall palindrome_hs :: CString -> CInt
foreign export ccall minclass_hs :: CString -> CInt -> CInt
foreign export ccall wordcheck_hs :: CString -> CString -> CInt
