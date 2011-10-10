{-| Hard-coded file paths used when building Pyon.
-}

module SetupPaths where

import System.FilePath

import Distribution.Simple
import Distribution.Simple.BuildPaths
import Distribution.Simple.LocalBuildInfo
import Distribution.PackageDescription

-- | The directories where source files belonging to the \"pyon\" program are
pyonSearchPaths :: LocalBuildInfo -> Executable -> [FilePath]
pyonSearchPaths lbi exe = autogenModulesDir lbi : hsSourceDirs (buildInfo exe)

-- | Destination for object files belonging to the \"pyon\" program
pyonBuildDir :: LocalBuildInfo -> FilePath
pyonBuildDir lbi = buildDir lbi </> "pyon"

-- | Directories containing source files belonging to the RTS
rtsSearchPaths :: LocalBuildInfo -> [FilePath]
rtsSearchPaths lbi =
  [ rtsBuildDir lbi                -- Compiled files
  , buildDir lbi </> "autogen"     -- Auto-generated files
  , dataBuildDir lbi </> "include" -- Predefined include files
  , "src/rts"                      -- Source files
  ]

-- | Destination for object files belonging to the RTS
rtsBuildDir :: LocalBuildInfo -> FilePath
rtsBuildDir lbi = buildDir lbi </> "rts"

-- | Destination for data files that will be installed
dataBuildDir :: LocalBuildInfo -> FilePath
dataBuildDir lbi = buildDir lbi </> "data"

-- | Directories containing source files belonging to the test driver
testDriverSearchPaths :: LocalBuildInfo -> [FilePath]
testDriverSearchPaths lbi = testDriverBuildDir lbi : ["src/testdriver"]

-- | Destination for the test driver files
testDriverBuildDir :: LocalBuildInfo -> FilePath
testDriverBuildDir lbi = buildDir lbi </> "testdriver"

-- | The test driver executable
testDriverProgram :: LocalBuildInfo -> FilePath
testDriverProgram lbi = testDriverBuildDir lbi </> "testdriver"

-- | Directory containing regression tests
testSourceDir = "test"

-- | Path to autogenerated makefile
cabalMakeFile :: FilePath
cabalMakeFile = "cabal.mk"

-- | C Source files used in RTS
rtsCSourceFiles = ["apply_data.c", "memory.c", "debug.c"]

-- | C++ Source files used in RTS
rtsCxxSourceFiles = ["par_loops.cc"]

-- | Pyon-asm files used in RTS
rtsPyAsmFiles = ["apply_new.pyasm",
                 "memory_py.pyasm",
                 "effects.pyasm",
                 "prim.pyasm", "structures.pyasm",
                 "complex.pyasm",
		 "list.pyasm", "stream.pyasm"]

-- | Data files that are not programmatically generated
prebuiltDataFiles = ["include/pyon.h", "include/pyon_list.h",
                     "include/pyon_matrix.h",
                     "include/PyonData.h",
                     "include/pyon/Base.h",
                     "include/pyon/Layout.h",
                     "symbols/corecode", "symbols/coretypes2"]
