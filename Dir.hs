{-# LANGUAGE ScopedTypeVariables #-}

module Dir where

import System.FilePath
import System.Directory
import Control.Exception

dirTree :: FilePath -> IO [FilePath]
dirTree f =
    do names <- getDirectoryContents f `catch` (\(_ :: IOException) -> return [])
       let paths = (map (f </>) . filter (`notElem` [".", ".."])) names
       recursed <- mapM dirTree paths
       return (f : concat recursed)
