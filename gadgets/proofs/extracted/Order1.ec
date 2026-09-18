require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_m4.

import SLH32.

require import
Array1 Array2 Array4 WArray4 WArray8 ArrayWords4W8 ArrayWords1W32
SubArrayDirect4W8_1W32 SubArrayDirect1W32_4W8.

module type Syscall_t = {
  proc randombytes_4 (_:W8.t Array4.t) : W8.t Array4.t
}.

module Syscall : Syscall_t = {
  proc randombytes_4 (a:W8.t Array4.t) : W8.t Array4.t = {
    
    a <$ (dmap WArray4.darray ArrayWords4W8.to_word_array);
    return a;
  }
}.

module M(SC:Syscall_t) = {
  proc _g_shl (y:W32.t Array2.t, x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    var inc:int;
    var i:int;
    var s:W32.t;
    var  _0:W32.t;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      s <- x.[i];
      s <- (s `<<` (truncateu8 a));
      y.[i] <- s;
      s <- (s `^` s);
      i <- (i + 1);
    }
     _0 <- (s `<<` (truncateu8 a));
    return y;
  }
  proc _g_shl_inplace (x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    var inc:int;
    var i:int;
    var s:W32.t;
    var  _0:W32.t;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      s <- x.[i];
      s <- (s `<<` (truncateu8 a));
      x.[i] <- s;
      s <- (s `^` s);
      i <- (i + 1);
    }
     _0 <- (s `<<` (truncateu8 a));
    return x;
  }
  proc _g_shr (y:W32.t Array2.t, x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    var inc:int;
    var i:int;
    var s:W32.t;
    var  _0:W32.t;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      s <- x.[i];
      s <- (s `>>` (truncateu8 a));
      y.[i] <- s;
      s <- (s `^` s);
      i <- (i + 1);
    }
     _0 <- (s `>>` (truncateu8 a));
    return y;
  }
  proc _g_shr_inplace (x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    var inc:int;
    var i:int;
    var s:W32.t;
    var  _0:W32.t;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      s <- x.[i];
      s <- (s `>>` (truncateu8 a));
      x.[i] <- s;
      s <- (s `^` s);
      i <- (i + 1);
    }
     _0 <- (s `>>` (truncateu8 a));
    return x;
  }
  proc _g_xor (c:W32.t Array2.t, a:W32.t Array2.t, b:W32.t Array2.t) : 
  W32.t Array2.t = {
    var inc:int;
    var i:int;
    var x:W32.t;
    var y:W32.t;
    var  _0:W32.t;
    var  _1:W32.t;
    a <- a;
    b <- b;
    c <- c;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      x <- a.[i];
      y <- b.[i];
      x <- (x `^` y);
      c.[i] <- x;
       _0 <- (x `^` x);
       _1 <- (y `^` y);
      i <- (i + 1);
    }
    return c;
  }
  proc _g_xor_inplace (a:W32.t Array2.t, b:W32.t Array2.t) : W32.t Array2.t = {
    var inc:int;
    var i:int;
    var x:W32.t;
    var y:W32.t;
    var  _0:W32.t;
    var  _1:W32.t;
    a <- a;
    b <- b;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      x <- a.[i];
      y <- b.[i];
      x <- (x `^` y);
      a.[i] <- x;
       _0 <- (x `^` x);
       _1 <- (y `^` y);
      i <- (i + 1);
    }
    return a;
  }
  proc _g_not (y:W32.t Array2.t, x:W32.t Array2.t) : W32.t Array2.t = {
    var inc:int;
    var s:W32.t;
    var i:int;
    var  _0:W32.t;
    var  _1:W32.t;
    y <- y;
    x <- x;
    s <- x.[0];
    s <- (s `^` (W32.of_int (- 1)));
    y.[0] <- s;
     _0 <- (s `^` s);
    inc <- (1 + 1);
    i <- 1;
    while ((i < inc)) {
      s <- x.[i];
      y.[i] <- s;
       _1 <- (s `^` s);
      i <- (i + 1);
    }
    return y;
  }
  proc _g_not_inplace (x:W32.t Array2.t) : W32.t Array2.t = {
    var s:W32.t;
    var  _0:W32.t;
    x <- x;
    s <- x.[0];
    s <- (s `^` (W32.of_int (- 1)));
    x.[0] <- s;
     _0 <- (s `^` s);
    return x;
  }
  proc _g_rolC (y:W32.t Array2.t, x:W32.t Array2.t, a:int) : W32.t Array2.t = {
    var inc:int;
    var i:int;
    var s:W32.t;
    var  _0:W32.t;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      s <- x.[i];
      s <- (s `|<<|` (W8.of_int a));
      y.[i] <- s;
      s <- (s `^` s);
      i <- (i + 1);
    }
     _0 <- (s `|<<|` (W8.of_int a));
    return y;
  }
  proc rol64 (res_hi:W32.t Array2.t, res_lo:W32.t Array2.t,
              x_hi:W32.t Array2.t, x_lo:W32.t Array2.t, a:int) : W32.t Array2.t *
                                                                 W32.t Array2.t = {
    var inc:int;
    var b:int;
    var shift:int;
    var i:int;
    var lo:W32.t;
    var hi:W32.t;
    var tmp:W32.t;
    var umsb:W32.t;
    var lmsb:W32.t;
    var  _0:W32.t;
    var  _1:W32.t;
    var  _2:W32.t;
    var  _3:W32.t;
    var  _4:W32.t;
    b <- (a %% 64);
    shift <- (b %% 32);
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      lo <- x_hi.[i];
      hi <- x_lo.[i];
      if ((32 < b)) {
        tmp <- lo;
        lo <- hi;
        hi <- tmp;
         _0 <- (tmp `^` tmp);
      } else {
        
      }
      umsb <- hi;
      umsb <- (umsb `>>` (W8.of_int (32 - shift)));
      lmsb <- lo;
      lmsb <- (lmsb `>>` (W8.of_int (32 - shift)));
      hi <- (hi `<<` (W8.of_int shift));
      lo <- (lo `<<` (W8.of_int shift));
      hi <- (hi `^` lmsb);
       _1 <- (lmsb `^` lmsb);
      lo <- (lo `^` umsb);
       _2 <- (umsb `^` umsb);
      res_hi.[i] <- lo;
      res_lo.[i] <- hi;
       _3 <- (lo `^` lo);
      hi <- (hi `^` hi);
      i <- (i + 1);
    }
     _4 <- (hi `<<` (W8.of_int 1));
    return (res_hi, res_lo);
  }
  proc rol64_1 (res_hi:W32.t Array2.t, res_lo:W32.t Array2.t,
                x_hi:W32.t Array2.t, x_lo:W32.t Array2.t) : W32.t Array2.t *
                                                            W32.t Array2.t = {
    
    (res_hi, res_lo) <@ rol64 (res_hi, res_lo, x_hi, x_lo, 1);
    return (res_hi, res_lo);
  }
  proc _g_and (c:W32.t Array2.t, a:W32.t Array2.t, b:W32.t Array2.t,
               randomness:W32.t Array1.t) : W32.t Array2.t = {
    var inc:int;
    var inc_0:int;
    var rand_counter:int;
    var i:int;
    var x:W32.t;
    var y:W32.t;
    var rand:W32.t;
    var j:int;
    var z:W32.t;
    var  _0:W32.t;
    var  _1:W32.t;
    var  _2:W32.t;
    var  _3:W32.t;
    var  _4:W32.t;
    var  _5:W32.t;
    var  _6:W32.t;
    var  _7:W32.t;
    c <- c;
    a <- a;
    b <- b;
    rand_counter <- 0;
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      x <- a.[i];
      y <- b.[i];
      x <- (x `&` y);
      c.[i] <- x;
       _0 <- (x `^` x);
       _1 <- (y `^` y);
      i <- (i + 1);
    }
    inc <- (1 + 1);
    i <- 0;
    while ((i < inc)) {
      inc_0 <- (1 + 1);
      j <- (i + 1);
      while ((j < inc_0)) {
        rand <- randomness.[rand_counter];
        rand_counter <- (rand_counter + 1);
        x <- c.[i];
        x <- (x `^` rand);
        c.[i] <- x;
         _2 <- (x `^` x);
        x <- a.[i];
        y <- b.[j];
        x <- (x `&` y);
        x <- (x `^` rand);
         _3 <- (rand `^` rand);
         _4 <- (y `^` y);
        y <- a.[j];
        z <- b.[i];
        y <- (y `&` z);
         _5 <- (z `^` z);
        x <- (x `^` y);
        y <- (y `^` y);
        y <- c.[j];
        x <- (x `^` y);
         _6 <- (y `^` y);
        c.[j] <- x;
         _7 <- (x `^` x);
        j <- (j + 1);
      }
      i <- (i + 1);
    }
    c <- c;
    return c;
  }
  proc _g_ref (c:W32.t Array2.t, a:W32.t Array2.t, randomness:W32.t Array1.t) : 
  W32.t Array2.t = {
    var inc:int;
    var x:W32.t;
    var one:W32.t Array2.t;
    var i:int;
    var onep:W32.t Array2.t;
    one <- witness;
    onep <- witness;
    x <- (W32.of_int (- 1));
    one.[0] <- x;
    x <- (W32.of_int 0);
    inc <- (1 + 1);
    i <- 1;
    while ((i < inc)) {
      one.[i] <- x;
      i <- (i + 1);
    }
    onep <- one;
    c <@ _g_and (c, a, onep, randomness);
    return c;
  }
  proc _g_share (res_0:W32.t Array2.t, x:W32.t, randomness:W32.t Array1.t) : 
  W32.t Array2.t = {
    var inc:int;
    var i:int;
    var r:W32.t;
    x <- x;
    inc <- ((1 + 1) - 1);
    i <- 0;
    while ((i < inc)) {
      r <- randomness.[i];
      res_0.[i] <- r;
      x <- (x `^` r);
      i <- (i + 1);
    }
    res_0.[((1 + 1) - 1)] <- x;
    return res_0;
  }
  proc _g_reconstruct (x:W32.t Array2.t) : W32.t = {
    var inc:int;
    var s:W32.t;
    var i:int;
    var a:W32.t;
    s <- x.[0];
    inc <- (1 + 1);
    i <- 1;
    while ((i < inc)) {
      a <- x.[i];
      s <- (s `^` a);
      i <- (i + 1);
    }
    return s;
  }
  proc lm_share (res_0:W32.t Array2.t, x:W32.t) : W32.t Array2.t = {
    var rand:W32.t Array1.t;
    var randp:W32.t Array1.t;
    var randpB:W8.t Array4.t;
    rand <- witness;
    randp <- witness;
    randpB <- witness;
    randp <- rand;
    randpB <- (SubArrayDirect4W8_1W32.get_sub randp 0);
    randpB <@ SC.randombytes_4 (randpB);
    randp <- (SubArrayDirect1W32_4W8.get_sub randpB 0);
    res_0 <@ _g_share (res_0, x, randp);
    return res_0;
  }
  proc lm_and (c:W32.t Array2.t, a:W32.t Array2.t, b:W32.t Array2.t) : 
  W32.t Array2.t = {
    var rand:W32.t Array1.t;
    var randp:W32.t Array1.t;
    var randpB:W8.t Array4.t;
    rand <- witness;
    randp <- witness;
    randpB <- witness;
    randp <- rand;
    randpB <- (SubArrayDirect4W8_1W32.get_sub randp 0);
    randpB <@ SC.randombytes_4 (randpB);
    randp <- (SubArrayDirect1W32_4W8.get_sub randpB 0);
    c <@ _g_and (c, a, b, randp);
    return c;
  }
  proc lm_ref (c:W32.t Array2.t, a:W32.t Array2.t) : W32.t Array2.t = {
    var rand:W32.t Array1.t;
    var randp:W32.t Array1.t;
    var randpB:W8.t Array4.t;
    rand <- witness;
    randp <- witness;
    randpB <- witness;
    randp <- rand;
    randpB <- (SubArrayDirect4W8_1W32.get_sub randp 0);
    randpB <@ SC.randombytes_4 (randpB);
    randp <- (SubArrayDirect1W32_4W8.get_sub randpB 0);
    c <@ _g_ref (c, a, randp);
    return c;
  }
  proc lm_share_derand (res_0:W32.t Array2.t, x:W32.t,
                        randomness:W32.t Array1.t) : W32.t Array2.t = {
    
    res_0 <@ _g_share (res_0, x, randomness);
    return res_0;
  }
  proc lm_reconstruct (x:W32.t Array2.t) : W32.t = {
    var res_0:W32.t;
    res_0 <@ _g_reconstruct (x);
    return res_0;
  }
  proc lm_get_order () : W32.t = {
    var r:W32.t;
    r <- (W32.of_int 1);
    return r;
  }
  proc lm_xor (c:W32.t Array2.t, a:W32.t Array2.t, b:W32.t Array2.t) : 
  W32.t Array2.t = {
    
    c <@ _g_xor (c, a, b);
    return c;
  }
  proc lm_xor_inplace (a:W32.t Array2.t, b:W32.t Array2.t) : W32.t Array2.t = {
    
    a <@ _g_xor_inplace (a, b);
    return a;
  }
  proc lm_not (y:W32.t Array2.t, x:W32.t Array2.t) : W32.t Array2.t = {
    
    y <@ _g_not (y, x);
    return y;
  }
  proc lm_not_inplace (x:W32.t Array2.t) : W32.t Array2.t = {
    
    x <@ _g_not_inplace (x);
    return x;
  }
  proc lm_shl (y:W32.t Array2.t, x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    
    y <@ _g_shl (y, x, a);
    return y;
  }
  proc lm_shl_inplace (x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    
    x <@ _g_shl_inplace (x, a);
    return x;
  }
  proc lm_shr (y:W32.t Array2.t, x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    
    y <@ _g_shr (y, x, a);
    return y;
  }
  proc lm_shr_inplace (x:W32.t Array2.t, a:W32.t) : W32.t Array2.t = {
    
    x <@ _g_shr_inplace (x, a);
    return x;
  }
  proc lm_and_derand (c:W32.t Array2.t, a:W32.t Array2.t, b:W32.t Array2.t,
                      randomness:W32.t Array1.t) : W32.t Array2.t = {
    
    c <@ _g_and (c, a, b, randomness);
    return c;
  }
  proc lm_ref_derand (c:W32.t Array2.t, a:W32.t Array2.t,
                      randomness:W32.t Array1.t) : W32.t Array2.t = {
    
    c <@ _g_ref (c, a, randomness);
    return c;
  }
  proc lm_rol64_1 (res_hi:W32.t Array2.t, res_lo:W32.t Array2.t,
                   x_hi:W32.t Array2.t, x_lo:W32.t Array2.t) : W32.t Array2.t *
                                                               W32.t Array2.t = {
    
    (res_hi, res_lo) <@ rol64_1 (res_hi, res_lo, x_hi, x_lo);
    return (res_hi, res_lo);
  }
}.
