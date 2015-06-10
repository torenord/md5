------------------------------------------------------------
-- The MD5 Message-Digest Algorithm
-- https://tools.ietf.org/html/rfc1321
------------------------------------------------------------

module Main where

import Data.Word
import Data.Char
import Numeric
import Data.Bits
import qualified Data.ByteString as B

type MDBuffer = (Word32, Word32, Word32, Word32)

-- Helper function

group :: Int -> [a] -> [[a]]
group 0 _  = []
group _ [] = []
group n lst = take n lst : group n (drop n lst)

-- A 64-element table T[1 ... 64] constructed from the sine function.

-- t :: (Integral a) => a -> Word32
-- t i | 0 <= i && i < 64 =
--   let n = fromIntegral (i+1)
--   in floor $ (abs $ sin $ n) * 2^32

t :: Int -> Word32
t i = [3614090360, 3905402710,  606105819, 3250441966, 4118548399, 1200080426, 2821735955, 4249261313,
       1770035416, 2336552879, 4294925233, 2304563134, 1804603682, 4254626195, 2792965006, 1236535329,
       4129170786, 3225465664,  643717713, 3921069994, 3593408605,   38016083, 3634488961, 3889429448,
        568446438, 3275163606, 4107603335, 1163531501, 2850285829, 4243563512, 1735328473, 2368359562,
       4294588738, 2272392833, 1839030562, 4259657740, 2763975236, 1272893353, 4139469664, 3200236656,
        681279174, 3936430074, 3572445317,   76029189, 3654602809, 3873151461,  530742520, 3299628645,
       4096336452, 1126891415, 2878612391, 4237533241, 1700485571, 2399980690, 4293915773, 2240044497,
       1873313359, 4264355552, 2734768916, 1309151649, 4149444226, 3174756917,  718787259, 3951481745] !! i

-- Round shifts

fshifts :: [Int]
gshifts :: [Int]
hshifts :: [Int]
ishifts :: [Int]

fshifts = 7 : 12 : 17 : 22 : fshifts
gshifts = 5 :  9 : 14 : 20 : gshifts
hshifts = 4 : 11 : 16 : 23 : hshifts
ishifts = 6 : 10 : 15 : 21 : ishifts

-- Step 1. Append Padding Bits

appendpaddingbit :: [Word8] -> [Word8]
appendpaddingbit buf = buf ++ [0x80]

appendzeros :: [Word8] -> [Word8]
appendzeros buf = buf ++ replicate ((64 - 8 - length buf) `mod` 64) 0

-- Step 2. Append Length

tolittleendian :: (Integral a) => a -> [Word8]
tolittleendian n = map (\i -> fromIntegral $ n `div` 2^(8*i)) [0..7]

appendlength :: (Integral a) => a -> [Word8] -> [Word8]
appendlength n buf = buf ++ tolittleendian n

initbuffer :: [Word8] -> [Word8]
initbuffer buf = appendlength (8 * length buf) $ appendzeros $ appendpaddingbit buf

-- Step 3. Initialize MD Buffer

a0 :: Word32
b0 :: Word32
c0 :: Word32
d0 :: Word32

a0 = 0x67452301
b0 = 0xefcdab89
c0 = 0x98badcfe
d0 = 0x10325476

-- Step 4. Process Message in 16-Word Blocks

-- Four auxiliary functions

ffun :: Word32 -> Word32 -> Word32 -> Word32
gfun :: Word32 -> Word32 -> Word32 -> Word32
hfun :: Word32 -> Word32 -> Word32 -> Word32
ifun :: Word32 -> Word32 -> Word32 -> Word32

ffun x y z = (x .&. y) .|. (complement x .&. z)
gfun x y z = (x .&. z) .|. (y .&. complement z)
hfun x y z = xor x $ xor y z
ifun x y z = xor y (x .|. complement z)

ff :: (Word32 -> t1 -> t -> Word32)
      -> [Word32]
      -> (Word32, Word32, t1, t)
      -> (Int, Int, Int)
      -> (t, Word32, Word32, t1)
ff fn str (a, b, c, d) (k, s, i) =
  let a' = b + (rotateL (a + (fn b c d) + str !! k + t i) s)
  in (d, a', b, c)

fargs :: Int -> (Int, Int, Int)
fargs i = (i, fshifts !! i, i)

gargs :: Int -> (Int, Int, Int)
gargs i = ((5*i + 1) `mod` 16, gshifts !! i, i)

hargs :: Int -> (Int, Int, Int)
hargs i = ((3*i + 5) `mod` 16, hshifts !! i, i)

iargs :: Int -> (Int, Int, Int)
iargs i = ((7*i) `mod` 16, ishifts !! i, i)

fog :: (t1 -> t -> t1) -> t1 -> [t] -> t1
fog _ abcd [] = abcd
fog func abcd (ksi:ksis) = fog func (func abcd ksi) ksis

fgo :: [Word32]
             -> (Word32, Word32, Word32, Word32)
             -> (Word32, Word32, Word32, Word32)
fgo str abcd = fog (ff ffun str) abcd (map fargs [0..15])

ggo :: [Word32]
             -> (Word32, Word32, Word32, Word32)
             -> (Word32, Word32, Word32, Word32)
ggo str abcd = fog (ff gfun str) abcd (map gargs [16..31])

hgo :: [Word32]
             -> (Word32, Word32, Word32, Word32)
             -> (Word32, Word32, Word32, Word32)
hgo str abcd = fog (ff hfun str) abcd (map hargs [32..47])

igo :: [Word32]
             -> (Word32, Word32, Word32, Word32)
             -> (Word32, Word32, Word32, Word32)
igo str abcd = fog (ff ifun str) abcd (map iargs [48..63])

rounds :: [Word32] -> MDBuffer -> MDBuffer
rounds buf abcd = (igo buf . hgo buf . ggo buf . fgo buf) abcd

process :: [[Word32]] -> MDBuffer -> MDBuffer
process [] abcd = abcd
process (buf:bufs) (a, b, c, d) =
  let (a', b', c', d') = rounds buf (a, b, c, d)
  in process bufs (a+a', b+b', c+c', d+d')

xss :: [Word8] -> [Word32]
xss [] = []
xss (x:xs) = (fromIntegral x) : (xss xs)

x :: [Word32] -> Word32
x xs = fromIntegral $ sum $ map (\x -> (fst x) * (snd x)) (zip (map (2^) [0,8..]) xs)

m :: [Word8] -> [Word32]
m s = map (x . xss) $ group 4 s

md5 :: [Word8] -> [Char]
md5 buf = printrr $ process (map m (group 64 $ initbuffer buf)) (a0, b0, c0, d0)

md5s :: [Char] -> [Char]
md5s str = md5 $ map (fromIntegral . ord) str

converthex :: (Integral a, Show a) => a -> [Char]
converthex n = let s = (showIntAtBase 16 intToDigit n "") in
  case s of
    _ | length s /= 8 -> (replicate (8 - length s) '0') ++ s
      | otherwise     -> s

func1 :: (Integral a, Show a) => a -> [Char]
func1 n = foldr (++) "" (reverse $ group 2 (converthex n))

printrr :: (Integral a, Show a) => (a, a, a, a) -> [Char]
printrr (a, b, c, d) = foldr (++) "" (map func1 [a, b, c, d])

tests :: Bool
tests =
  and [md5s "" == "d41d8cd98f00b204e9800998ecf8427e",
       md5s "a" == "0cc175b9c0f1b6a831c399e269772661",
       md5s "abc" == "900150983cd24fb0d6963f7d28e17f72",
       md5s "message digest" == "f96b697d7cb7938d525a2f31aaf161d0",
       md5s "abcdefghijklmnopqrstuvwxyz" == "c3fcd3d76192e4007dfb496cca67e13b"]

main :: IO ()
main = do contents <- B.getContents
          putStr $ (if not tests then "!!! Tests: Not OK !!!\n" else "")
          putStrLn $ md5 $ B.unpack contents
