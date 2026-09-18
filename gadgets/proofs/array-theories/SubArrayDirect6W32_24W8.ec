from Jasmin require import JWord JWord_array.

require import ArrayWords6W32 ArrayWords24W8.

clone export SubArrayCast as SubArrayDirect6W32_24W8  with op sizeWS <- 4,
                                                           op sizeWB <- 1,
                                                           op sizeS <- 6,
                                                           op sizeB <- 24,
                                                           theory WordS <- W32,
                                                           theory WordB <- W8,
                                                           theory ArrayWordsS <= ArrayWords6W32,
                                                           theory ArrayWordsB <= ArrayWords24W8.
