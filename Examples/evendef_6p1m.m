(* Created with the Wolfram Language : www.wolfram.com *)
evenSixPOneM = {w[1] -> Log[mm], w[2] -> Log[mm + s234 - s56 - s61], 
    w[3] -> Log[mm - s56], w[4] -> Log[mm - s61], 
    w[5] -> Log[mm*s12*s345 - mm*s123*s345 - s12*s123*s345 + s123^2*s345 + 
       s123*s345^2 - mm*s12*s45 + s12^2*s45 + mm*s123*s45 - s12*s123*s45 - 
       s12*s345*s45 - s123*s345*s45 + s12*s45^2], 
    w[6] -> Log[mm*s123 - mm*s56 - s123*s56 + s45*s56 + s56^2], 
    w[7] -> Log[mm*s123*s34 - s123*s345*s56 + s12*s45*s56], 
    w[8] -> Log[mm*s23 - s123*s61], 
    w[9] -> Log[mm*s23*s345 - s123*s345*s61 + s12*s45*s61], 
    w[10] -> Log[mm*s234 - s56*s61], w[11] -> Log[mm*s34 - s345*s56], 
    w[12] -> Log[mm*s345 - mm*s61 + s12*s61 - s345*s61 + s61^2], 
    w[13] -> Log[mm^2*s23 - mm*s123*s23 + mm*s23^2 + mm*s123*s45 - 
       mm*s23*s45 - mm*s123*s61 + s123^2*s61 - mm*s23*s61 - s123*s23*s61 - 
       s123*s45*s61 + s23*s45*s61 + s123*s61^2], 
    w[14] -> Log[mm^2*s23^2*s34 - mm*s12*s23^2*s34 - mm^2*s23*s234*s34 + 
       mm*s12*s23*s234*s34 + mm*s123*s23*s234*s34 - s12*s123*s23*s234*s34 + 
       mm^2*s23*s34^2 - mm*s123*s23*s34^2 + mm*s23^2*s34^2 + 
       mm*s12*s23^2*s345 - 2*mm*s12*s23*s234*s345 + mm*s123*s23*s234*s345 + 
       s12*s123*s23*s234*s345 + mm*s12*s234^2*s345 - mm*s123*s234^2*s345 - 
       s12*s123*s234^2*s345 + s123^2*s234^2*s345 + mm*s123*s23*s34*s345 - 
       mm*s23^2*s34*s345 + mm*s123*s234*s34*s345 - s123^2*s234*s34*s345 + 
       mm*s23*s234*s34*s345 + s123*s23*s234*s34*s345 + s123^2*s234*s345^2 - 
       s123*s23*s234*s345^2 + s123*s234^2*s345^2 + mm*s12*s23*s234*s45 - 
       s12^2*s23*s234*s45 - mm*s12*s234^2*s45 + s12^2*s234^2*s45 + 
       mm*s123*s234^2*s45 - s12*s123*s234^2*s45 + mm*s12*s23*s34*s45 + 
       mm*s12*s234*s34*s45 - 2*mm*s123*s234*s34*s45 + s12*s123*s234*s34*s45 + 
       mm*s23*s234*s34*s45 + s12*s23*s234*s34*s45 + mm*s123*s34^2*s45 - 
       mm*s23*s34^2*s45 - 2*s12*s123*s234*s345*s45 + s12*s23*s234*s345*s45 - 
       s12*s234^2*s345*s45 - s123*s234^2*s345*s45 + s123*s234*s34*s345*s45 - 
       s23*s234*s34*s345*s45 + s12^2*s234*s45^2 + s12*s234^2*s45^2 - 
       s12*s234*s34*s45^2 - mm*s23^2*s34*s56 + s12*s23^2*s34*s56 - 
       mm*s23^2*s345*s56 - s12*s23^2*s345*s56 + mm*s23*s234*s345*s56 + 
       s12*s23*s234*s345*s56 - 2*s123*s23*s234*s345*s56 - 
       2*mm*s23*s34*s345*s56 + s123*s23*s34*s345*s56 - s23^2*s34*s345*s56 - 
       s123*s23*s345^2*s56 + s23^2*s345^2*s56 - s123*s234*s345^2*s56 - 
       s23*s234*s345^2*s56 - mm*s23*s234*s45*s56 + s12*s23*s234*s45*s56 + 
       mm*s23*s34*s45*s56 - 2*s12*s23*s34*s45*s56 + s12*s23*s345*s45*s56 + 
       s12*s234*s345*s45*s56 + s123*s234*s345*s45*s56 + 
       s23*s234*s345*s45*s56 - s123*s34*s345*s45*s56 + s23*s34*s345*s45*s56 - 
       s12*s234*s45^2*s56 + s12*s34*s45^2*s56 + s23^2*s345*s56^2 + 
       s23*s345^2*s56^2 - s23*s345*s45*s56^2 + mm*s12*s23*s34*s61 - 
       2*mm*s123*s23*s34*s61 + s12*s123*s23*s34*s61 - mm*s12*s234*s34*s61 + 
       mm*s123*s234*s34*s61 + s12*s123*s234*s34*s61 - s123^2*s234*s34*s61 - 
       mm*s123*s34^2*s61 + s123^2*s34^2*s61 - mm*s23*s34^2*s61 - 
       s123*s23*s34^2*s61 - s12*s123*s23*s345*s61 + s12*s123*s234*s345*s61 - 
       s123^2*s234*s345*s61 - s123^2*s34*s345*s61 + s123*s23*s34*s345*s61 - 
       2*s123*s234*s34*s345*s61 + s12^2*s23*s45*s61 - s12^2*s234*s45*s61 + 
       s12*s123*s234*s45*s61 + s12*s123*s34*s45*s61 - 2*s12*s23*s34*s45*s61 + 
       s12*s234*s34*s45*s61 + s123*s234*s34*s45*s61 - s123*s34^2*s45*s61 + 
       s23*s34^2*s45*s61 + mm*s23*s34*s56*s61 - 2*s12*s23*s34*s56*s61 + 
       s123*s23*s34*s56*s61 + s12*s23*s345*s56*s61 + s123*s23*s345*s56*s61 - 
       s12*s234*s345*s56*s61 + s123*s234*s345*s56*s61 + 
       s123*s34*s345*s56*s61 + s23*s34*s345*s56*s61 - 2*s12*s23*s45*s56*s61 + 
       s12*s234*s45*s56*s61 - s123*s234*s45*s56*s61 - 2*s12*s34*s45*s56*s61 + 
       s123*s34*s45*s56*s61 - 2*s23*s34*s45*s56*s61 - s23*s345*s56^2*s61 + 
       s23*s45*s56^2*s61 - s12*s123*s34*s61^2 + s123^2*s34*s61^2 + 
       s123*s34^2*s61^2 + s12*s34*s56*s61^2 - s123*s34*s56*s61^2], 
    w[15] -> Log[mm^2*s34 - mm*s12*s34 + mm*s34^2 + mm*s12*s345 - 
       mm*s34*s345 - mm*s34*s56 + s12*s34*s56 - mm*s345*s56 - s12*s345*s56 - 
       s34*s345*s56 + s345^2*s56 + s345*s56^2], w[16] -> Log[s12], 
    w[17] -> Log[s12 - s123], w[18] -> Log[s12 - s123 + s23], 
    w[19] -> Log[s12*s123 - s123^2 - s123*s34 - s12*s56 + s123*s56], 
    w[20] -> Log[s12*s234 + s234^2 - s234*s34 - s234*s56 + s34*s56], 
    w[21] -> Log[-(s123*s345) + s12*s45], w[22] -> Log[s123], 
    w[23] -> Log[s123 - s23], w[24] -> Log[s123 - s23 + s234 - s56], 
    w[25] -> Log[s123 - s56], w[26] -> Log[s123*s234 - s23*s56], 
    w[27] -> Log[s23], w[28] -> Log[s23 - s234], 
    w[29] -> Log[s23 - s234 + s34], 
    w[30] -> Log[s23*s234 - s234^2 - s234*s45 - s23*s61 + s234*s61], 
    w[31] -> Log[s23*s345 + s345^2 - s345*s45 - s345*s61 + s45*s61], 
    w[32] -> Log[s234], w[33] -> Log[s234 - s34], 
    w[34] -> Log[s234 - s34 + s345 - s61], w[35] -> Log[s234 - s56], 
    w[36] -> Log[s234 - s61], w[37] -> Log[s234*s345 - s34*s61], 
    w[38] -> Log[s34], w[39] -> Log[s34 - s345], 
    w[40] -> Log[s34 - s345 + s45], w[41] -> Log[s345], 
    w[42] -> Log[s345 - s45], w[43] -> Log[s345 - s61], w[44] -> Log[s45], 
    w[45] -> Log[s56], w[46] -> Log[s61]}
