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
palindrome_hs = fromIntegral . palindrome_c . unsafePerformIO . peekCString

minclass_hs :: CString -> CInt -> CInt
minclass_hs s m = (fromIntegral (minclass_c (unsafePerformIO (peekCString s)) (fromIntegral m)))
 
wordcheck_hs :: CString -> CString -> CInt
wordcheck_hs h n = (fromIntegral (wordcheck_c (unsafePerformIO (peekCString h)) (unsafePerformIO (peekCString n)))))
 
similar_hs :: CString -> CString -> CInt -> CInt
similar_hs h n d = (fromIntegral (similar_c (unsafePerformIO (peekCString h)) (unsafePerformIO (peekCString n)) (fromIntegral d)))
 
sequence_hs :: CString -> CInt -> CInt
sequence_hs s m = (fromIntegral (sequence_c (unsafePerformIO (peekCString s)) (fromIntegral m)))
 
consecutive_hs :: CString -> CInt -> CInt
consecutive_hs s m = (fromIntegral (consecutive_c (unsafePerformIO (peekCString s)) (fromIntegral m)))

foreign export ccall palindrome_hs :: CString -> CInt
foreign export ccall minclass_hs :: CString -> CInt -> CInt
foreign export ccall wordcheck_hs :: CString -> CString -> CInt
foreign export ccall similar_hs :: CString -> CString -> CInt -> CInt
foreign export ccall sequence_hs :: CString -> CInt -> CInt
foreign export ccall consecutive_hs :: CString -> CInt -> CInt
