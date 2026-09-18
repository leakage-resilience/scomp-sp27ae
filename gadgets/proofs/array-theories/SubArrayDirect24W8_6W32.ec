from Jasmin require import JWord JWord_array.

require import ArrayWords24W8 ArrayWords6W32.

clone export SubArrayCast as SubArrayDirect24W8_6W32  with op sizeWS <- 1,
                                                           op sizeWB <- 4,
                                                           op sizeS <- 24,
                                                           op sizeB <- 6,
                                                           theory WordS <- W8,
                                                           theory WordB <- W32,
                                                           theory ArrayWordsS <= ArrayWords24W8,
                                                           theory ArrayWordsB <= ArrayWords6W32.
