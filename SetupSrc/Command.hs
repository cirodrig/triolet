{-| Command line commands.

This file mainly takes care of managing various data formats for 'Command's
and the following data types, which interact with commands.

* The 'Program' and 'ConfiguredProgram' types used by Cabal to represent
  executables

* Plain strings, which hold command-line options
-}

module SetupSrc.Command where

import Control.Monad.Trans
import qualified Development.Shake as Shake
import Distribution.Simple.Program
import Distribution.Simple.Utils
import Distribution.Verbosity

-- | An invocation of a program, packaged up and ready to run
data Command =
    -- | An invocation of a Cabal program
    CabalCommand
    { cmdProgram   :: !ConfiguredProgram
    , cmdVerbosity :: !Verbosity
    , cmdArgs      :: ![ProgArg]
    }
    -- | An invocation of a program whose name is looked up by the shell
  | ShellCommand
    { cmdString    :: !FilePath
    , cmdVerbosity :: !Verbosity
    , cmdArgs      :: ![ProgArg]
    }

invokeProgram :: Verbosity -> ConfiguredProgram -> [ProgArg] -> Command
invokeProgram verb prog args = CabalCommand prog verb args

invokeString :: Verbosity -> FilePath -> [ProgArg] -> Command
invokeString verb prog args = ShellCommand prog verb args

runCommand :: Command -> Shake.Action ()
runCommand (CabalCommand prog verb args) =
  liftIO $ runProgram verb prog args

runCommand (ShellCommand prog verb args) =
  liftIO $ rawSystemExit verb prog args

-- | Add a prefix to a program argument
prefixProgArg :: String -> String -> String
prefixProgArg pfx arg = pfx ++ arg

-- | Add a prefix to a list of program arguments
prefixProgArgs :: String -> [String] -> [String]
prefixProgArgs pfx args = map (prefixProgArg pfx) args

-- | Add a flag before each of a list of program arguments
leadProgArgs :: String -> [String] -> [String]
leadProgArgs pfx (arg:args) = pfx:arg:leadProgArgs pfx args
leadProgArgs _   []         = []

prefixHaskellPaths = prefixProgArgs "-i"
prefixIncludePaths = prefixProgArgs "-I"
prefixLibraryPaths = prefixProgArgs "-L"
prefixLibraries = prefixProgArgs "-l"

