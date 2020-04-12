import Test.DocTest

main = doctest ["-ilib", 
                "lib/Data/RBR.hs",
                "lib/Data/RBR/Subset.hs",
                "lib/Data/RBR/Examples.hs",
                "lib/Data/RBR/Internal.hs"
               ]
