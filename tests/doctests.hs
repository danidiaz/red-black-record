import Test.DocTest

main = doctest ["-ilib", 
                "lib/Data/RBR.hs",
                "lib/Data/RBR/Examples.hs"
               ]
