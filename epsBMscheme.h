#procedure EpsRepBM
*
* Traces with 8 Fermions  
* (all identities in this file are from FeynCalc in Breit-Maison scheme)
*

id g_(2,6_,mu1?,mu2?,mu3?,mu4?,mu5?,mu6?,mu7?,mu8?)= -2 *d_(mu1,mu7)*d_(mu2,mu8) *d_(mu3,mu4)*d_(mu5,mu6) + 2 *d_(mu1,mu8)*d_(mu2,mu7) *d_(mu3,mu4)*d_(mu5,mu6) + 
  2 *d_(mu1,mu6)*d_(mu2,mu8) *d_(mu3,mu4)*d_(mu5,mu7) - 2 *d_(mu1,mu8)*d_(mu2,mu6) *d_(mu3,mu4)*d_(mu5,mu7) - 
  2 *d_(mu1,mu6)*d_(mu2,mu7) *d_(mu3,mu4)*d_(mu5,mu8) + 2 *d_(mu1,mu7)*d_(mu2,mu6) *d_(mu3,mu4)*d_(mu5,mu8) - 
  2 *d_(mu1,mu5)*d_(mu2,mu8) *d_(mu3,mu4)*d_(mu6,mu7) + 2 *d_(mu1,mu8)*d_(mu2,mu5) *d_(mu3,mu4)*d_(mu6,mu7) + 
  2 *d_(mu1,mu5)*d_(mu2,mu7) *d_(mu3,mu4)*d_(mu6,mu8) - 2 *d_(mu1,mu7)*d_(mu2,mu5) *d_(mu3,mu4)*d_(mu6,mu8) - 
  2 *d_(mu1,mu5)*d_(mu2,mu6) *d_(mu3,mu4)*d_(mu7,mu8) + 2 *d_(mu1,mu6)*d_(mu2,mu5) *d_(mu3,mu4)*d_(mu7,mu8) + 
  2 *d_(mu1,mu7)*d_(mu2,mu8) *d_(mu3,mu5)*d_(mu4,mu6) - 2 *d_(mu1,mu8)*d_(mu2,mu7) *d_(mu3,mu5)*d_(mu4,mu6) - 
  2 *d_(mu1,mu6)*d_(mu2,mu8) *d_(mu3,mu5)*d_(mu4,mu7) + 2 *d_(mu1,mu8)*d_(mu2,mu6) *d_(mu3,mu5)*d_(mu4,mu7) + 
  2 *d_(mu1,mu6)*d_(mu2,mu7) *d_(mu3,mu5)*d_(mu4,mu8) - 2 *d_(mu1,mu7)*d_(mu2,mu6) *d_(mu3,mu5)*d_(mu4,mu8) + 
  2 *d_(mu1,mu4)*d_(mu2,mu8) *d_(mu3,mu5)*d_(mu6,mu7) - 2 *d_(mu1,mu8)*d_(mu2,mu4) *d_(mu3,mu5)*d_(mu6,mu7) - 
  2 *d_(mu1,mu4)*d_(mu2,mu7) *d_(mu3,mu5)*d_(mu6,mu8) + 2 *d_(mu1,mu7)*d_(mu2,mu4) *d_(mu3,mu5)*d_(mu6,mu8) + 
  2 *d_(mu1,mu4)*d_(mu2,mu6) *d_(mu3,mu5)*d_(mu7,mu8) - 2 *d_(mu1,mu6)*d_(mu2,mu4) *d_(mu3,mu5)*d_(mu7,mu8) - 
  2 *d_(mu1,mu7)*d_(mu2,mu8) *d_(mu3,mu6)*d_(mu4,mu5) + 2 *d_(mu1,mu8)*d_(mu2,mu7) *d_(mu3,mu6)*d_(mu4,mu5) + 
  2 *d_(mu1,mu5)*d_(mu2,mu8) *d_(mu3,mu6)*d_(mu4,mu7) - 2 *d_(mu1,mu8)*d_(mu2,mu5) *d_(mu3,mu6)*d_(mu4,mu7) - 
  2 *d_(mu1,mu5)*d_(mu2,mu7) *d_(mu3,mu6)*d_(mu4,mu8) + 2 *d_(mu1,mu7)*d_(mu2,mu5) *d_(mu3,mu6)*d_(mu4,mu8) - 
  2 *d_(mu1,mu4)*d_(mu2,mu8) *d_(mu3,mu6)*d_(mu5,mu7) + 2 *d_(mu1,mu8)*d_(mu2,mu4) *d_(mu3,mu6)*d_(mu5,mu7) + 
  2 *d_(mu1,mu4)*d_(mu2,mu7) *d_(mu3,mu6)*d_(mu5,mu8) - 2 *d_(mu1,mu7)*d_(mu2,mu4) *d_(mu3,mu6)*d_(mu5,mu8) - 
  2 *d_(mu1,mu4)*d_(mu2,mu5) *d_(mu3,mu6)*d_(mu7,mu8) + 2 *d_(mu1,mu5)*d_(mu2,mu4) *d_(mu3,mu6)*d_(mu7,mu8) + 
  2 *d_(mu1,mu6)*d_(mu2,mu8) *d_(mu3,mu7)*d_(mu4,mu5) - 2 *d_(mu1,mu8)*d_(mu2,mu6) *d_(mu3,mu7)*d_(mu4,mu5) - 
  2 *d_(mu1,mu5)*d_(mu2,mu8) *d_(mu3,mu7)*d_(mu4,mu6) + 2 *d_(mu1,mu8)*d_(mu2,mu5) *d_(mu3,mu7)*d_(mu4,mu6) + 
  2 *d_(mu1,mu5)*d_(mu2,mu6) *d_(mu3,mu7)*d_(mu4,mu8) - 2 *d_(mu1,mu6)*d_(mu2,mu5) *d_(mu3,mu7)*d_(mu4,mu8) + 
  2 *d_(mu1,mu4)*d_(mu2,mu8) *d_(mu3,mu7)*d_(mu5,mu6) - 2 *d_(mu1,mu8)*d_(mu2,mu4) *d_(mu3,mu7)*d_(mu5,mu6) - 
  2 *d_(mu1,mu4)*d_(mu2,mu6) *d_(mu3,mu7)*d_(mu5,mu8) + 2 *d_(mu1,mu6)*d_(mu2,mu4) *d_(mu3,mu7)*d_(mu5,mu8) + 
  2 *d_(mu1,mu4)*d_(mu2,mu5) *d_(mu3,mu7)*d_(mu6,mu8) - 2 *d_(mu1,mu5)*d_(mu2,mu4) *d_(mu3,mu7)*d_(mu6,mu8) - 
  2 *d_(mu1,mu6)*d_(mu2,mu7) *d_(mu3,mu8)*d_(mu4,mu5) + 2 *d_(mu1,mu7)*d_(mu2,mu6) *d_(mu3,mu8)*d_(mu4,mu5) + 
  2 *d_(mu1,mu5)*d_(mu2,mu7) *d_(mu3,mu8)*d_(mu4,mu6) - 2 *d_(mu1,mu7)*d_(mu2,mu5) *d_(mu3,mu8)*d_(mu4,mu6) - 
  2 *d_(mu1,mu5)*d_(mu2,mu6) *d_(mu3,mu8)*d_(mu4,mu7) + 2 *d_(mu1,mu6)*d_(mu2,mu5) *d_(mu3,mu8)*d_(mu4,mu7) - 
  2 *d_(mu1,mu4)*d_(mu2,mu7) *d_(mu3,mu8)*d_(mu5,mu6) + 2 *d_(mu1,mu7)*d_(mu2,mu4) *d_(mu3,mu8)*d_(mu5,mu6) + 
  2 *d_(mu1,mu4)*d_(mu2,mu6) *d_(mu3,mu8)*d_(mu5,mu7) - 2 *d_(mu1,mu6)*d_(mu2,mu4) *d_(mu3,mu8)*d_(mu5,mu7) - 
  2 *d_(mu1,mu4)*d_(mu2,mu5) *d_(mu3,mu8)*d_(mu6,mu7) + 2 *d_(mu1,mu5)*d_(mu2,mu4) *d_(mu3,mu8)*d_(mu6,mu7) + 
  2 *d_(mu1,mu2)*d_(mu3,mu8) *d_(mu4,mu5)*d_(mu6,mu7) - 2 *d_(mu1,mu3)*d_(mu2,mu8) *d_(mu4,mu5)*d_(mu6,mu7) + 
  2 *d_(mu1,mu8)*d_(mu2,mu3) *d_(mu4,mu5)*d_(mu6,mu7) - 2 *d_(mu1,mu2)*d_(mu3,mu7) *d_(mu4,mu5)*d_(mu6,mu8) + 
  2 *d_(mu1,mu3)*d_(mu2,mu7) *d_(mu4,mu5)*d_(mu6,mu8) - 2 *d_(mu1,mu7)*d_(mu2,mu3) *d_(mu4,mu5)*d_(mu6,mu8) + 
  2 *d_(mu1,mu2)*d_(mu3,mu6) *d_(mu4,mu5)*d_(mu7,mu8) - 2 *d_(mu1,mu3)*d_(mu2,mu6) *d_(mu4,mu5)*d_(mu7,mu8) + 
  2 *d_(mu1,mu6)*d_(mu2,mu3) *d_(mu4,mu5)*d_(mu7,mu8) - 2 *d_(mu1,mu2)*d_(mu3,mu8) *d_(mu4,mu6)*d_(mu5,mu7) + 
  2 *d_(mu1,mu3)*d_(mu2,mu8) *d_(mu4,mu6)*d_(mu5,mu7) - 2 *d_(mu1,mu8)*d_(mu2,mu3) *d_(mu4,mu6)*d_(mu5,mu7) + 
  2 *d_(mu1,mu2)*d_(mu3,mu7) *d_(mu4,mu6)*d_(mu5,mu8) - 2 *d_(mu1,mu3)*d_(mu2,mu7) *d_(mu4,mu6)*d_(mu5,mu8) + 
  2 *d_(mu1,mu7)*d_(mu2,mu3) *d_(mu4,mu6)*d_(mu5,mu8) - 2 *d_(mu1,mu2)*d_(mu3,mu5) *d_(mu4,mu6)*d_(mu7,mu8) + 
  2 *d_(mu1,mu3)*d_(mu2,mu5) *d_(mu4,mu6)*d_(mu7,mu8) - 2 *d_(mu1,mu5)*d_(mu2,mu3) *d_(mu4,mu6)*d_(mu7,mu8) + 
  2 *d_(mu1,mu2)*d_(mu3,mu8) *d_(mu4,mu7)*d_(mu5,mu6) - 2 *d_(mu1,mu3)*d_(mu2,mu8) *d_(mu4,mu7)*d_(mu5,mu6) + 
  2 *d_(mu1,mu8)*d_(mu2,mu3) *d_(mu4,mu7)*d_(mu5,mu6) - 2 *d_(mu1,mu2)*d_(mu3,mu6) *d_(mu4,mu7)*d_(mu5,mu8) + 
  2 *d_(mu1,mu3)*d_(mu2,mu6) *d_(mu4,mu7)*d_(mu5,mu8) - 2 *d_(mu1,mu6)*d_(mu2,mu3) *d_(mu4,mu7)*d_(mu5,mu8) + 
  2 *d_(mu1,mu2)*d_(mu3,mu5) *d_(mu4,mu7)*d_(mu6,mu8) - 2 *d_(mu1,mu3)*d_(mu2,mu5) *d_(mu4,mu7)*d_(mu6,mu8) + 
  2 *d_(mu1,mu5)*d_(mu2,mu3) *d_(mu4,mu7)*d_(mu6,mu8) - 2 *d_(mu1,mu2)*d_(mu3,mu7) *d_(mu4,mu8)*d_(mu5,mu6) + 
  2 *d_(mu1,mu3)*d_(mu2,mu7) *d_(mu4,mu8)*d_(mu5,mu6) - 2 *d_(mu1,mu7)*d_(mu2,mu3) *d_(mu4,mu8)*d_(mu5,mu6) + 
  2 *d_(mu1,mu2)*d_(mu3,mu6) *d_(mu4,mu8)*d_(mu5,mu7) - 2 *d_(mu1,mu3)*d_(mu2,mu6) *d_(mu4,mu8)*d_(mu5,mu7) + 
  2 *d_(mu1,mu6)*d_(mu2,mu3) *d_(mu4,mu8)*d_(mu5,mu7) - 2 *d_(mu1,mu2)*d_(mu3,mu5) *d_(mu4,mu8)*d_(mu6,mu7) + 
  2 *d_(mu1,mu3)*d_(mu2,mu5) *d_(mu4,mu8)*d_(mu6,mu7) - 2 *d_(mu1,mu5)*d_(mu2,mu3) *d_(mu4,mu8)*d_(mu6,mu7) + 
  2 *d_(mu1,mu2)*d_(mu3,mu4) *d_(mu5,mu6)*d_(mu7,mu8) - 2 *d_(mu1,mu3)*d_(mu2,mu4) *d_(mu5,mu6)*d_(mu7,mu8) + 
  2 *d_(mu1,mu4)*d_(mu2,mu3) *d_(mu5,mu6)*d_(mu7,mu8) - 2 *d_(mu1,mu2)*d_(mu3,mu4) *d_(mu5,mu7)*d_(mu6,mu8) + 
  2 *d_(mu1,mu3)*d_(mu2,mu4) *d_(mu5,mu7)*d_(mu6,mu8) - 2 *d_(mu1,mu4)*d_(mu2,mu3) *d_(mu5,mu7)*d_(mu6,mu8) + 
  2 *d_(mu1,mu2)*d_(mu3,mu4) *d_(mu5,mu8)*d_(mu6,mu7) - 2 *d_(mu1,mu3)*d_(mu2,mu4) *d_(mu5,mu8)*d_(mu6,mu7) + 
  2 *d_(mu1,mu4)*d_(mu2,mu3) *d_(mu5,mu8)*d_(mu6,mu7) - 2 *i *d_(mu5,mu6)*d_(mu7,mu8) *e_(mu1,mu2,mu3,mu4) + 
  2 *i *d_(mu5,mu7)*d_(mu6,mu8) *e_(mu1,mu2,mu3,mu4) - 2 *i *d_(mu5,mu8)*d_(mu6,mu7) *e_(mu1,mu2,mu3,mu4) + 
  2 *i *d_(mu4,mu6)*d_(mu7,mu8) *e_(mu1,mu2,mu3,mu5) - 2 *i *d_(mu4,mu7)*d_(mu6,mu8) *e_(mu1,mu2,mu3,mu5) + 
  2 *i *d_(mu4,mu8)*d_(mu6,mu7) *e_(mu1,mu2,mu3,mu5) - 2 *i *d_(mu4,mu5)*d_(mu7,mu8) *e_(mu1,mu2,mu3,mu6) + 
  2 *i *d_(mu4,mu7)*d_(mu5,mu8) *e_(mu1,mu2,mu3,mu6) - 2 *i *d_(mu4,mu8)*d_(mu5,mu7) *e_(mu1,mu2,mu3,mu6) + 
  2 *i *d_(mu4,mu5)*d_(mu6,mu8) *e_(mu1,mu2,mu3,mu7) - 2 *i *d_(mu4,mu6)*d_(mu5,mu8) *e_(mu1,mu2,mu3,mu7) + 
  2 *i *d_(mu4,mu8)*d_(mu5,mu6) *e_(mu1,mu2,mu3,mu7) - 2 *i *d_(mu4,mu5)*d_(mu6,mu7) *e_(mu1,mu2,mu3,mu8) + 
  2 *i *d_(mu4,mu6)*d_(mu5,mu7) *e_(mu1,mu2,mu3,mu8) - 2 *i *d_(mu4,mu7)*d_(mu5,mu6) *e_(mu1,mu2,mu3,mu8) - 
  2 *i *d_(mu3,mu6)*d_(mu7,mu8) *e_(mu1,mu2,mu4,mu5) + 2 *i *d_(mu3,mu7)*d_(mu6,mu8) *e_(mu1,mu2,mu4,mu5) - 
  2 *i *d_(mu3,mu8)*d_(mu6,mu7) *e_(mu1,mu2,mu4,mu5) + 2 *i *d_(mu3,mu5)*d_(mu7,mu8) *e_(mu1,mu2,mu4,mu6) - 
  2 *i *d_(mu3,mu7)*d_(mu5,mu8) *e_(mu1,mu2,mu4,mu6) + 2 *i *d_(mu3,mu8)*d_(mu5,mu7) *e_(mu1,mu2,mu4,mu6) - 
  2 *i *d_(mu3,mu5)*d_(mu6,mu8) *e_(mu1,mu2,mu4,mu7) + 2 *i *d_(mu3,mu6)*d_(mu5,mu8) *e_(mu1,mu2,mu4,mu7) - 
  2 *i *d_(mu3,mu8)*d_(mu5,mu6) *e_(mu1,mu2,mu4,mu7) + 2 *i *d_(mu3,mu5)*d_(mu6,mu7) *e_(mu1,mu2,mu4,mu8) - 
  2 *i *d_(mu3,mu6)*d_(mu5,mu7) *e_(mu1,mu2,mu4,mu8) + 2 *i *d_(mu3,mu7)*d_(mu5,mu6) *e_(mu1,mu2,mu4,mu8) - 
  2 *i *d_(mu3,mu4)*d_(mu7,mu8) *e_(mu1,mu2,mu5,mu6) + 2 *i *d_(mu3,mu7)*d_(mu4,mu8) *e_(mu1,mu2,mu5,mu6) - 
  2 *i *d_(mu3,mu8)*d_(mu4,mu7) *e_(mu1,mu2,mu5,mu6) + 2 *i *d_(mu3,mu4)*d_(mu6,mu8) *e_(mu1,mu2,mu5,mu7) - 
  2 *i *d_(mu3,mu6)*d_(mu4,mu8) *e_(mu1,mu2,mu5,mu7) + 2 *i *d_(mu3,mu8)*d_(mu4,mu6) *e_(mu1,mu2,mu5,mu7) - 
  2 *i *d_(mu3,mu4)*d_(mu6,mu7) *e_(mu1,mu2,mu5,mu8) + 2 *i *d_(mu3,mu6)*d_(mu4,mu7) *e_(mu1,mu2,mu5,mu8) - 
  2 *i *d_(mu3,mu7)*d_(mu4,mu6) *e_(mu1,mu2,mu5,mu8) - 2 *i *d_(mu3,mu4)*d_(mu5,mu8) *e_(mu1,mu2,mu6,mu7) + 
  2 *i *d_(mu3,mu5)*d_(mu4,mu8) *e_(mu1,mu2,mu6,mu7) - 2 *i *d_(mu3,mu8)*d_(mu4,mu5) *e_(mu1,mu2,mu6,mu7) + 
  2 *i *d_(mu3,mu4)*d_(mu5,mu7) *e_(mu1,mu2,mu6,mu8) - 2 *i *d_(mu3,mu5)*d_(mu4,mu7) *e_(mu1,mu2,mu6,mu8) + 
  2 *i *d_(mu3,mu7)*d_(mu4,mu5) *e_(mu1,mu2,mu6,mu8) - 2 *i *d_(mu3,mu4)*d_(mu5,mu6) *e_(mu1,mu2,mu7,mu8) + 
  2 *i *d_(mu3,mu5)*d_(mu4,mu6) *e_(mu1,mu2,mu7,mu8) - 2 *i *d_(mu3,mu6)*d_(mu4,mu5) *e_(mu1,mu2,mu7,mu8) + 
  2 *i *d_(mu2,mu6)*d_(mu7,mu8) *e_(mu1,mu3,mu4,mu5) - 2 *i *d_(mu2,mu7)*d_(mu6,mu8) *e_(mu1,mu3,mu4,mu5) + 
  2 *i *d_(mu2,mu8)*d_(mu6,mu7) *e_(mu1,mu3,mu4,mu5) - 2 *i *d_(mu2,mu5)*d_(mu7,mu8) *e_(mu1,mu3,mu4,mu6) + 
  2 *i *d_(mu2,mu7)*d_(mu5,mu8) *e_(mu1,mu3,mu4,mu6) - 2 *i *d_(mu2,mu8)*d_(mu5,mu7) *e_(mu1,mu3,mu4,mu6) + 
  2 *i *d_(mu2,mu5)*d_(mu6,mu8) *e_(mu1,mu3,mu4,mu7) - 2 *i *d_(mu2,mu6)*d_(mu5,mu8) *e_(mu1,mu3,mu4,mu7) + 
  2 *i *d_(mu2,mu8)*d_(mu5,mu6) *e_(mu1,mu3,mu4,mu7) - 2 *i *d_(mu2,mu5)*d_(mu6,mu7) *e_(mu1,mu3,mu4,mu8) + 
  2 *i *d_(mu2,mu6)*d_(mu5,mu7) *e_(mu1,mu3,mu4,mu8) - 2 *i *d_(mu2,mu7)*d_(mu5,mu6) *e_(mu1,mu3,mu4,mu8) + 
  2 *i *d_(mu2,mu4)*d_(mu7,mu8) *e_(mu1,mu3,mu5,mu6) - 2 *i *d_(mu2,mu7)*d_(mu4,mu8) *e_(mu1,mu3,mu5,mu6) + 
  2 *i *d_(mu2,mu8)*d_(mu4,mu7) *e_(mu1,mu3,mu5,mu6) - 2 *i *d_(mu2,mu4)*d_(mu6,mu8) *e_(mu1,mu3,mu5,mu7) + 
  2 *i *d_(mu2,mu6)*d_(mu4,mu8) *e_(mu1,mu3,mu5,mu7) - 2 *i *d_(mu2,mu8)*d_(mu4,mu6) *e_(mu1,mu3,mu5,mu7) + 
  2 *i *d_(mu2,mu4)*d_(mu6,mu7) *e_(mu1,mu3,mu5,mu8) - 2 *i *d_(mu2,mu6)*d_(mu4,mu7) *e_(mu1,mu3,mu5,mu8) + 
  2 *i *d_(mu2,mu7)*d_(mu4,mu6) *e_(mu1,mu3,mu5,mu8) + 2 *i *d_(mu2,mu4)*d_(mu5,mu8) *e_(mu1,mu3,mu6,mu7) - 
  2 *i *d_(mu2,mu5)*d_(mu4,mu8) *e_(mu1,mu3,mu6,mu7) + 2 *i *d_(mu2,mu8)*d_(mu4,mu5) *e_(mu1,mu3,mu6,mu7) - 
  2 *i *d_(mu2,mu4)*d_(mu5,mu7) *e_(mu1,mu3,mu6,mu8) + 2 *i *d_(mu2,mu5)*d_(mu4,mu7) *e_(mu1,mu3,mu6,mu8) - 
  2 *i *d_(mu2,mu7)*d_(mu4,mu5) *e_(mu1,mu3,mu6,mu8) + 2 *i *d_(mu2,mu4)*d_(mu5,mu6) *e_(mu1,mu3,mu7,mu8) - 
  2 *i *d_(mu2,mu5)*d_(mu4,mu6) *e_(mu1,mu3,mu7,mu8) + 2 *i *d_(mu2,mu6)*d_(mu4,mu5) *e_(mu1,mu3,mu7,mu8) - 
  2 *i *d_(mu2,mu3)*d_(mu7,mu8) *e_(mu1,mu4,mu5,mu6) + 2 *i *d_(mu2,mu7)*d_(mu3,mu8) *e_(mu1,mu4,mu5,mu6) - 
  2 *i *d_(mu2,mu8)*d_(mu3,mu7) *e_(mu1,mu4,mu5,mu6) + 2 *i *d_(mu2,mu3)*d_(mu6,mu8) *e_(mu1,mu4,mu5,mu7) - 
  2 *i *d_(mu2,mu6)*d_(mu3,mu8) *e_(mu1,mu4,mu5,mu7) + 2 *i *d_(mu2,mu8)*d_(mu3,mu6) *e_(mu1,mu4,mu5,mu7) - 
  2 *i *d_(mu2,mu3)*d_(mu6,mu7) *e_(mu1,mu4,mu5,mu8) + 2 *i *d_(mu2,mu6)*d_(mu3,mu7) *e_(mu1,mu4,mu5,mu8) - 
  2 *i *d_(mu2,mu7)*d_(mu3,mu6) *e_(mu1,mu4,mu5,mu8) - 2 *i *d_(mu2,mu3)*d_(mu5,mu8) *e_(mu1,mu4,mu6,mu7) + 
  2 *i *d_(mu2,mu5)*d_(mu3,mu8) *e_(mu1,mu4,mu6,mu7) - 2 *i *d_(mu2,mu8)*d_(mu3,mu5) *e_(mu1,mu4,mu6,mu7) + 
  2 *i *d_(mu2,mu3)*d_(mu5,mu7) *e_(mu1,mu4,mu6,mu8) - 2 *i *d_(mu2,mu5)*d_(mu3,mu7) *e_(mu1,mu4,mu6,mu8) + 
  2 *i *d_(mu2,mu7)*d_(mu3,mu5) *e_(mu1,mu4,mu6,mu8) - 2 *i *d_(mu2,mu3)*d_(mu5,mu6) *e_(mu1,mu4,mu7,mu8) + 
  2 *i *d_(mu2,mu5)*d_(mu3,mu6) *e_(mu1,mu4,mu7,mu8) - 2 *i *d_(mu2,mu6)*d_(mu3,mu5) *e_(mu1,mu4,mu7,mu8) + 
  2 *i *d_(mu2,mu3)*d_(mu4,mu8) *e_(mu1,mu5,mu6,mu7) - 2 *i *d_(mu2,mu4)*d_(mu3,mu8) *e_(mu1,mu5,mu6,mu7) + 
  2 *i *d_(mu2,mu8)*d_(mu3,mu4) *e_(mu1,mu5,mu6,mu7) - 2 *i *d_(mu2,mu3)*d_(mu4,mu7) *e_(mu1,mu5,mu6,mu8) + 
  2 *i *d_(mu2,mu4)*d_(mu3,mu7) *e_(mu1,mu5,mu6,mu8) - 2 *i *d_(mu2,mu7)*d_(mu3,mu4) *e_(mu1,mu5,mu6,mu8) + 
  2 *i *d_(mu2,mu3)*d_(mu4,mu6) *e_(mu1,mu5,mu7,mu8) - 2 *i *d_(mu2,mu4)*d_(mu3,mu6) *e_(mu1,mu5,mu7,mu8) + 
  2 *i *d_(mu2,mu6)*d_(mu3,mu4) *e_(mu1,mu5,mu7,mu8) - 2 *i *d_(mu2,mu3)*d_(mu4,mu5) *e_(mu1,mu6,mu7,mu8) + 
  2 *i *d_(mu2,mu4)*d_(mu3,mu5) *e_(mu1,mu6,mu7,mu8) - 2 *i *d_(mu2,mu5)*d_(mu3,mu4) *e_(mu1,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu6)*d_(mu7,mu8) *e_(mu2,mu3,mu4,mu5) + 2 *i *d_(mu1,mu7)*d_(mu6,mu8) *e_(mu2,mu3,mu4,mu5) - 
  2 *i *d_(mu1,mu8)*d_(mu6,mu7) *e_(mu2,mu3,mu4,mu5) + 2 *i *d_(mu1,mu5)*d_(mu7,mu8) *e_(mu2,mu3,mu4,mu6) - 
  2 *i *d_(mu1,mu7)*d_(mu5,mu8) *e_(mu2,mu3,mu4,mu6) + 2 *i *d_(mu1,mu8)*d_(mu5,mu7) *e_(mu2,mu3,mu4,mu6) - 
  2 *i *d_(mu1,mu5)*d_(mu6,mu8) *e_(mu2,mu3,mu4,mu7) + 2 *i *d_(mu1,mu6)*d_(mu5,mu8) *e_(mu2,mu3,mu4,mu7) - 
  2 *i *d_(mu1,mu8)*d_(mu5,mu6) *e_(mu2,mu3,mu4,mu7) + 2 *i *d_(mu1,mu5)*d_(mu6,mu7) *e_(mu2,mu3,mu4,mu8) - 
  2 *i *d_(mu1,mu6)*d_(mu5,mu7) *e_(mu2,mu3,mu4,mu8) + 2 *i *d_(mu1,mu7)*d_(mu5,mu6) *e_(mu2,mu3,mu4,mu8) - 
  2 *i *d_(mu1,mu4)*d_(mu7,mu8) *e_(mu2,mu3,mu5,mu6) + 2 *i *d_(mu1,mu7)*d_(mu4,mu8) *e_(mu2,mu3,mu5,mu6) - 
  2 *i *d_(mu1,mu8)*d_(mu4,mu7) *e_(mu2,mu3,mu5,mu6) + 2 *i *d_(mu1,mu4)*d_(mu6,mu8) *e_(mu2,mu3,mu5,mu7) - 
  2 *i *d_(mu1,mu6)*d_(mu4,mu8) *e_(mu2,mu3,mu5,mu7) + 2 *i *d_(mu1,mu8)*d_(mu4,mu6) *e_(mu2,mu3,mu5,mu7) - 
  2 *i *d_(mu1,mu4)*d_(mu6,mu7) *e_(mu2,mu3,mu5,mu8) + 2 *i *d_(mu1,mu6)*d_(mu4,mu7) *e_(mu2,mu3,mu5,mu8) - 
  2 *i *d_(mu1,mu7)*d_(mu4,mu6) *e_(mu2,mu3,mu5,mu8) - 2 *i *d_(mu1,mu4)*d_(mu5,mu8) *e_(mu2,mu3,mu6,mu7) + 
  2 *i *d_(mu1,mu5)*d_(mu4,mu8) *e_(mu2,mu3,mu6,mu7) - 2 *i *d_(mu1,mu8)*d_(mu4,mu5) *e_(mu2,mu3,mu6,mu7) + 
  2 *i *d_(mu1,mu4)*d_(mu5,mu7) *e_(mu2,mu3,mu6,mu8) - 2 *i *d_(mu1,mu5)*d_(mu4,mu7) *e_(mu2,mu3,mu6,mu8) + 
  2 *i *d_(mu1,mu7)*d_(mu4,mu5) *e_(mu2,mu3,mu6,mu8) - 2 *i *d_(mu1,mu4)*d_(mu5,mu6) *e_(mu2,mu3,mu7,mu8) + 
  2 *i *d_(mu1,mu5)*d_(mu4,mu6) *e_(mu2,mu3,mu7,mu8) - 2 *i *d_(mu1,mu6)*d_(mu4,mu5) *e_(mu2,mu3,mu7,mu8) + 
  2 *i *d_(mu1,mu3)*d_(mu7,mu8) *e_(mu2,mu4,mu5,mu6) - 2 *i *d_(mu1,mu7)*d_(mu3,mu8) *e_(mu2,mu4,mu5,mu6) + 
  2 *i *d_(mu1,mu8)*d_(mu3,mu7) *e_(mu2,mu4,mu5,mu6) - 2 *i *d_(mu1,mu3)*d_(mu6,mu8) *e_(mu2,mu4,mu5,mu7) + 
  2 *i *d_(mu1,mu6)*d_(mu3,mu8) *e_(mu2,mu4,mu5,mu7) - 2 *i *d_(mu1,mu8)*d_(mu3,mu6) *e_(mu2,mu4,mu5,mu7) + 
  2 *i *d_(mu1,mu3)*d_(mu6,mu7) *e_(mu2,mu4,mu5,mu8) - 2 *i *d_(mu1,mu6)*d_(mu3,mu7) *e_(mu2,mu4,mu5,mu8) + 
  2 *i *d_(mu1,mu7)*d_(mu3,mu6) *e_(mu2,mu4,mu5,mu8) + 2 *i *d_(mu1,mu3)*d_(mu5,mu8) *e_(mu2,mu4,mu6,mu7) - 
  2 *i *d_(mu1,mu5)*d_(mu3,mu8) *e_(mu2,mu4,mu6,mu7) + 2 *i *d_(mu1,mu8)*d_(mu3,mu5) *e_(mu2,mu4,mu6,mu7) - 
  2 *i *d_(mu1,mu3)*d_(mu5,mu7) *e_(mu2,mu4,mu6,mu8) + 2 *i *d_(mu1,mu5)*d_(mu3,mu7) *e_(mu2,mu4,mu6,mu8) - 
  2 *i *d_(mu1,mu7)*d_(mu3,mu5) *e_(mu2,mu4,mu6,mu8) + 2 *i *d_(mu1,mu3)*d_(mu5,mu6) *e_(mu2,mu4,mu7,mu8) - 
  2 *i *d_(mu1,mu5)*d_(mu3,mu6) *e_(mu2,mu4,mu7,mu8) + 2 *i *d_(mu1,mu6)*d_(mu3,mu5) *e_(mu2,mu4,mu7,mu8) - 
  2 *i *d_(mu1,mu3)*d_(mu4,mu8) *e_(mu2,mu5,mu6,mu7) + 2 *i *d_(mu1,mu4)*d_(mu3,mu8) *e_(mu2,mu5,mu6,mu7) - 
  2 *i *d_(mu1,mu8)*d_(mu3,mu4) *e_(mu2,mu5,mu6,mu7) + 2 *i *d_(mu1,mu3)*d_(mu4,mu7) *e_(mu2,mu5,mu6,mu8) - 
  2 *i *d_(mu1,mu4)*d_(mu3,mu7) *e_(mu2,mu5,mu6,mu8) + 2 *i *d_(mu1,mu7)*d_(mu3,mu4) *e_(mu2,mu5,mu6,mu8) - 
  2 *i *d_(mu1,mu3)*d_(mu4,mu6) *e_(mu2,mu5,mu7,mu8) + 2 *i *d_(mu1,mu4)*d_(mu3,mu6) *e_(mu2,mu5,mu7,mu8) - 
  2 *i *d_(mu1,mu6)*d_(mu3,mu4) *e_(mu2,mu5,mu7,mu8) + 2 *i *d_(mu1,mu3)*d_(mu4,mu5) *e_(mu2,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu4)*d_(mu3,mu5) *e_(mu2,mu6,mu7,mu8) + 2 *i *d_(mu1,mu5)*d_(mu3,mu4) *e_(mu2,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu2)*d_(mu7,mu8) *e_(mu3,mu4,mu5,mu6) + 2 *i *d_(mu1,mu7)*d_(mu2,mu8) *e_(mu3,mu4,mu5,mu6) - 
  2 *i *d_(mu1,mu8)*d_(mu2,mu7) *e_(mu3,mu4,mu5,mu6) + 2 *i *d_(mu1,mu2)*d_(mu6,mu8) *e_(mu3,mu4,mu5,mu7) - 
  2 *i *d_(mu1,mu6)*d_(mu2,mu8) *e_(mu3,mu4,mu5,mu7) + 2 *i *d_(mu1,mu8)*d_(mu2,mu6) *e_(mu3,mu4,mu5,mu7) - 
  2 *i *d_(mu1,mu2)*d_(mu6,mu7) *e_(mu3,mu4,mu5,mu8) + 2 *i *d_(mu1,mu6)*d_(mu2,mu7) *e_(mu3,mu4,mu5,mu8) - 
  2 *i *d_(mu1,mu7)*d_(mu2,mu6) *e_(mu3,mu4,mu5,mu8) - 2 *i *d_(mu1,mu2)*d_(mu5,mu8) *e_(mu3,mu4,mu6,mu7) + 
  2 *i *d_(mu1,mu5)*d_(mu2,mu8) *e_(mu3,mu4,mu6,mu7) - 2 *i *d_(mu1,mu8)*d_(mu2,mu5) *e_(mu3,mu4,mu6,mu7) + 
  2 *i *d_(mu1,mu2)*d_(mu5,mu7) *e_(mu3,mu4,mu6,mu8) - 2 *i *d_(mu1,mu5)*d_(mu2,mu7) *e_(mu3,mu4,mu6,mu8) + 
  2 *i *d_(mu1,mu7)*d_(mu2,mu5) *e_(mu3,mu4,mu6,mu8) - 2 *i *d_(mu1,mu2)*d_(mu5,mu6) *e_(mu3,mu4,mu7,mu8) + 
  2 *i *d_(mu1,mu5)*d_(mu2,mu6) *e_(mu3,mu4,mu7,mu8) - 2 *i *d_(mu1,mu6)*d_(mu2,mu5) *e_(mu3,mu4,mu7,mu8) + 
  2 *i *d_(mu1,mu2)*d_(mu4,mu8) *e_(mu3,mu5,mu6,mu7) - 2 *i *d_(mu1,mu4)*d_(mu2,mu8) *e_(mu3,mu5,mu6,mu7) + 
  2 *i *d_(mu1,mu8)*d_(mu2,mu4) *e_(mu3,mu5,mu6,mu7) - 2 *i *d_(mu1,mu2)*d_(mu4,mu7) *e_(mu3,mu5,mu6,mu8) + 
  2 *i *d_(mu1,mu4)*d_(mu2,mu7) *e_(mu3,mu5,mu6,mu8) - 2 *i *d_(mu1,mu7)*d_(mu2,mu4) *e_(mu3,mu5,mu6,mu8) + 
  2 *i *d_(mu1,mu2)*d_(mu4,mu6) *e_(mu3,mu5,mu7,mu8) - 2 *i *d_(mu1,mu4)*d_(mu2,mu6) *e_(mu3,mu5,mu7,mu8) + 
  2 *i *d_(mu1,mu6)*d_(mu2,mu4) *e_(mu3,mu5,mu7,mu8) - 2 *i *d_(mu1,mu2)*d_(mu4,mu5) *e_(mu3,mu6,mu7,mu8) + 
  2 *i *d_(mu1,mu4)*d_(mu2,mu5) *e_(mu3,mu6,mu7,mu8) - 2 *i *d_(mu1,mu5)*d_(mu2,mu4) *e_(mu3,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu2)*d_(mu3,mu8) *e_(mu4,mu5,mu6,mu7) + 2 *i *d_(mu1,mu3)*d_(mu2,mu8) *e_(mu4,mu5,mu6,mu7) - 
  2 *i *d_(mu1,mu8)*d_(mu2,mu3) *e_(mu4,mu5,mu6,mu7) + 2 *i *d_(mu1,mu2)*d_(mu3,mu7) *e_(mu4,mu5,mu6,mu8) - 
  2 *i *d_(mu1,mu3)*d_(mu2,mu7) *e_(mu4,mu5,mu6,mu8) + 2 *i *d_(mu1,mu7)*d_(mu2,mu3) *e_(mu4,mu5,mu6,mu8) - 
  2 *i *d_(mu1,mu2)*d_(mu3,mu6) *e_(mu4,mu5,mu7,mu8) + 2 *i *d_(mu1,mu3)*d_(mu2,mu6) *e_(mu4,mu5,mu7,mu8) - 
  2 *i *d_(mu1,mu6)*d_(mu2,mu3) *e_(mu4,mu5,mu7,mu8) + 2 *i *d_(mu1,mu2)*d_(mu3,mu5) *e_(mu4,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu3)*d_(mu2,mu5) *e_(mu4,mu6,mu7,mu8) + 2 *i *d_(mu1,mu5)*d_(mu2,mu3) *e_(mu4,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu2)*d_(mu3,mu4) *e_(mu5,mu6,mu7,mu8) + 2 *i *d_(mu1,mu3)*d_(mu2,mu4) *e_(mu5,mu6,mu7,mu8) - 
  2 *i *d_(mu1,mu4)*d_(mu2,mu3) *e_(mu5,mu6,mu7,mu8);

  
*
* Traces with 6 Fermions
*

id g_(1,6_,mu1?,mu2?,mu3?,mu4?,mu5?,mu6?)= 2 *d_(mu1,mu6) *d_(mu2,mu5) *d_(mu3,mu4) - 2 *d_(mu1,mu5) *d_(mu2,mu6) *d_(mu3,mu4) - 2 *d_(mu1,mu6) *d_(mu2,mu4) *d_(mu3,mu5) + 
  2 *d_(mu1,mu4) *d_(mu2,mu6) *d_(mu3,mu5) + 2 *d_(mu1,mu5) *d_(mu2,mu4) *d_(mu3,mu6) - 2 *d_(mu1,mu4) *d_(mu2,mu5) *d_(mu3,mu6) + 
  2 *d_(mu1,mu6) *d_(mu2,mu3) *d_(mu4,mu5) - 2 *d_(mu1,mu3) *d_(mu2,mu6) *d_(mu4,mu5) + 2 *d_(mu1,mu2) *d_(mu3,mu6) *d_(mu4,mu5) - 
  2 *d_(mu1,mu5) *d_(mu2,mu3) *d_(mu4,mu6) + 2 *d_(mu1,mu3) *d_(mu2,mu5) *d_(mu4,mu6) - 2 *d_(mu1,mu2) *d_(mu3,mu5) *d_(mu4,mu6) + 
  2 *d_(mu1,mu4) *d_(mu2,mu3) *d_(mu5,mu6) - 2 *d_(mu1,mu3) *d_(mu2,mu4) *d_(mu5,mu6) + 2 *d_(mu1,mu2) *d_(mu3,mu4) *d_(mu5,mu6) - 
  2 *i *d_(mu5,mu6) *e_(mu1,mu2,mu3,mu4) + 2 *i *d_(mu4,mu6) *e_(mu1,mu2,mu3,mu5) - 2 *i *d_(mu4,mu5) *e_(mu1,mu2,mu3,mu6) - 
  2 *i *d_(mu3,mu6) *e_(mu1,mu2,mu4,mu5) + 2 *i *d_(mu3,mu5) *e_(mu1,mu2,mu4,mu6) - 2 *i *d_(mu3,mu4) *e_(mu1,mu2,mu5,mu6) + 
  2 *i *d_(mu2,mu6) *e_(mu1,mu3,mu4,mu5) - 2 *i *d_(mu2,mu5) *e_(mu1,mu3,mu4,mu6) + 2 *i *d_(mu2,mu4) *e_(mu1,mu3,mu5,mu6) - 
  2 *i *d_(mu2,mu3) *e_(mu1,mu4,mu5,mu6) - 2 *i *d_(mu1,mu6) *e_(mu2,mu3,mu4,mu5) + 2 *i *d_(mu1,mu5) *e_(mu2,mu3,mu4,mu6) - 
  2 *i *d_(mu1,mu4) *e_(mu2,mu3,mu5,mu6) + 2 *i *d_(mu1,mu3) *e_(mu2,mu4,mu5,mu6) - 2 *i *d_(mu1,mu2) *e_(mu3,mu4,mu5,mu6);
  
id g_(2,6_,mu1?,mu2?,mu3?,mu4?,mu5?,mu6?)= 2 *d_(mu1,mu6) *d_(mu2,mu5) *d_(mu3,mu4) - 2 *d_(mu1,mu5) *d_(mu2,mu6) *d_(mu3,mu4) - 2 *d_(mu1,mu6) *d_(mu2,mu4) *d_(mu3,mu5) + 
  2 *d_(mu1,mu4) *d_(mu2,mu6) *d_(mu3,mu5) + 2 *d_(mu1,mu5) *d_(mu2,mu4) *d_(mu3,mu6) - 2 *d_(mu1,mu4) *d_(mu2,mu5) *d_(mu3,mu6) + 
  2 *d_(mu1,mu6) *d_(mu2,mu3) *d_(mu4,mu5) - 2 *d_(mu1,mu3) *d_(mu2,mu6) *d_(mu4,mu5) + 2 *d_(mu1,mu2) *d_(mu3,mu6) *d_(mu4,mu5) - 
  2 *d_(mu1,mu5) *d_(mu2,mu3) *d_(mu4,mu6) + 2 *d_(mu1,mu3) *d_(mu2,mu5) *d_(mu4,mu6) - 2 *d_(mu1,mu2) *d_(mu3,mu5) *d_(mu4,mu6) + 
  2 *d_(mu1,mu4) *d_(mu2,mu3) *d_(mu5,mu6) - 2 *d_(mu1,mu3) *d_(mu2,mu4) *d_(mu5,mu6) + 2 *d_(mu1,mu2) *d_(mu3,mu4) *d_(mu5,mu6) - 
  2 *i *d_(mu5,mu6) *e_(mu1,mu2,mu3,mu4) + 2 *i *d_(mu4,mu6) *e_(mu1,mu2,mu3,mu5) - 2 *i *d_(mu4,mu5) *e_(mu1,mu2,mu3,mu6) - 
  2 *i *d_(mu3,mu6) *e_(mu1,mu2,mu4,mu5) + 2 *i *d_(mu3,mu5) *e_(mu1,mu2,mu4,mu6) - 2 *i *d_(mu3,mu4) *e_(mu1,mu2,mu5,mu6) + 
  2 *i *d_(mu2,mu6) *e_(mu1,mu3,mu4,mu5) - 2 *i *d_(mu2,mu5) *e_(mu1,mu3,mu4,mu6) + 2 *i *d_(mu2,mu4) *e_(mu1,mu3,mu5,mu6) - 
  2 *i *d_(mu2,mu3) *e_(mu1,mu4,mu5,mu6) - 2 *i *d_(mu1,mu6) *e_(mu2,mu3,mu4,mu5) + 2 *i *d_(mu1,mu5) *e_(mu2,mu3,mu4,mu6) - 
  2 *i *d_(mu1,mu4) *e_(mu2,mu3,mu5,mu6) + 2 *i *d_(mu1,mu3) *e_(mu2,mu4,mu5,mu6) - 2 *i *d_(mu1,mu2) *e_(mu3,mu4,mu5,mu6); 
  
#endprocedure  
  
  
