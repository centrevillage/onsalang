#pragma STDC FP_CONTRACT OFF
float f(float a, float b, float c){ return (float)((float)(a*b) + c); }
float g(float a, float b, float c){ return a*b + c; }
