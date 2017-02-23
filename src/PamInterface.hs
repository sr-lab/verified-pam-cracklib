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
 
foreign export ccall palindrome_hs :: CString -> CInt
