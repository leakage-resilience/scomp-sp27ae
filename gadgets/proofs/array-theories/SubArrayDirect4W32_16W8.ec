from Jasmin require import JWord JWord_array.

require import ArrayWords4W32 ArrayWords16W8.

clone export SubArrayCast as SubArrayDirect4W32_16W8  with op sizeWS <- 4,
                                                           op sizeWB <- 1,
                                                           op sizeS <- 4,
                                                           op sizeB <- 16,
                                                           theory WordS <- W32,
                                                           theory WordB <- W8,
                                                           theory ArrayWordsS <= ArrayWords4W32,
                                                           theory ArrayWordsB <= ArrayWords16W8.
