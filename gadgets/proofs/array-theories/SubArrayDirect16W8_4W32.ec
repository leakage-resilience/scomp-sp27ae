from Jasmin require import JWord JWord_array.

require import ArrayWords16W8 ArrayWords4W32.

clone export SubArrayCast as SubArrayDirect16W8_4W32  with op sizeWS <- 1,
                                                           op sizeWB <- 4,
                                                           op sizeS <- 16,
                                                           op sizeB <- 4,
                                                           theory WordS <- W8,
                                                           theory WordB <- W32,
                                                           theory ArrayWordsS <= ArrayWords16W8,
                                                           theory ArrayWordsB <= ArrayWords4W32.
