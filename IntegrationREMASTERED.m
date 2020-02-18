(* ::Package:: *)

gramdetTH = s12^2 s34^2+ s13^2 s24^2+s14^2 s23^2 -2 s12 s34 s13 s24 - 2 s12 s34 s14 s23 - 2 s13 s24 s14 s23;
hyperreg=  Hypergeometric2F1Regularized[a_,b_,c_,d_]->Hypergeometric2F1[a,b,c,d]/Gamma[c];
barback ={zbar->1-z,xbar->1-x,vbar->1-v,wbar->1-w,ubar->1-u};
fullcovariables = {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2*Sqrt[vbar w wbar x xbar]) z};
gdTH2 = 4^(d-4) (z (zbar))^(d-3) (u*(ubar))^((d-5)/2) v^(d-3) (vbar)^((d-4)/2) (w)^((d-4)/2) (wbar)^((d-4)/2) (x)^((d-4)/2) (xbar)^((d-4)/2) /. d-> 4-2\[Epsilon]// Simplify;
denoms={Den[q1+q4]->1/s14,Den[q2+q4]->1/s24,Den[q3+q4]->1/s34,Den[q1+q2+q3]->1/(s12+s13+s23)};


(* ::Section::Closed:: *)
(*vergleich der Integrale vor und nach Reduktion*)


Int=1/((k1)^2 (k1+p1+p2-pb)^2 (k1+p2)^2 (pb-p1-p2)^4 (p1)^2 p2^2 p3^2 (pb-p1-p2-p3)^2)  /. 1/(-p1-p2-p3+pb)^2->1  /. 1/p1^2->1 /. 1/p2^2->1 /. 1/p3^2->1


{(k1)^2,(k1+p1+p2-pb)^2,(k1+p2)^2,(pb-p1-p2)^2,(p1)^2,p2^2,p3^2,(pb-p1-p2-p3)^2,(k1+p3)^2,(k1+pb)^2,(p1+pb)^2,(p2+pb)^2,(p3+pb)^2,(p2+p3)^2};


-(((-8+3 d) (-18+5 d) (-16+5 d) (-14+5 d) G[2,{0,1,1,0,1,1,1,1,0,0,0,0,0,0}])/((-6+d) (-4+d)^2 (-14+3 d) pb^6))+(4 (-7+2 d) (-5+2 d) (-18+5 d) (-16+5 d) (-14+5 d) (-12+5 d) G[2,{1,0,1,0,1,0,1,1,0,0,0,0,0,0}])/((-6+d) (-5+d) (-4+d)^2 (-3+d) (-14+3 d) pb^8)+(8 (-3+d) (-7+2 d) (-18+5 d) (-16+5 d) (-14+5 d) G[2,{1,1,0,0,1,1,1,1,0,0,0,0,0,0}])/(3 (-5+d) (-4+d)^2 (-14+3 d) (-10+3 d) pb^6)


Int2=((-8+3 d) (-18+5 d) (-16+5 d) (-14+5 d) )/((-6+d) (-4+d)^2 (-14+3 d) pb^6)*1/((k1+p1+p2-pb)^2 (k1+p2)^2)


factorB1=((-8+3 d) (-18+5 d) (-16+5 d) (-14+5 d) )/((-6+d) (-4+d)^2 (-14+3 d) pb^6)


factorB2=((8 (-3+d) (-7+2 d) (-18+5 d) (-16+5 d) (-14+5 d) )/(3 (-5+d) (-4+d)^2 (-14+3 d) (-10+3 d) pb^6  )) 


Int3=((8 (-3+d) (-7+2 d) (-18+5 d) (-16+5 d) (-14+5 d) )/(3 (-5+d) (-4+d)^2 (-14+3 d) (-10+3 d) pb^6 (k1)^2 (k1+p1+p2-pb)^2 )) 


(* ::Subsection:: *)
(*C0 (vor Red)*)


xintC=Assuming[{1>a>0,1>c>0,1>b>0,0<\[Epsilon]},Integrate[(a+b x)^(-1-\[Epsilon]),{x,0,1}]]


xintC2=Refine[ExpandAll[Simplify[xintC  /. b-> s23+s24 /. a->  s34 ] /. p12^2-> s12]  /. p1*p4->s14/2 /. p2*p4->s24/2 /. p4^2-> 0 ,s12>0] // Simplify


yintcoeffC=Integrate[(y^a1*(1-y)^a2),{y,0,1}] /. {a1-> -1-\[Epsilon],a2->-\[Epsilon]}


yintcoeffC2=(Gamma[1-\[Epsilon]] Gamma[-\[Epsilon]])/Gamma[1-2 \[Epsilon]]// Simplify





(*variables123cyclic = {s23->v w z,s14->vbar zbar,s24->v x zbar,s13->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2/Sqrt[vbar w wbar x xbar]) z};*)


gdTH=4^(-4+d) v^2 Sqrt[vbar w wbar x xbar] z^2 zbar^2 (-u ubar v^2 vbar w wbar x xbar z^2 zbar^2)^(1/2 (-5+d))// Factor // Simplify;


gdTH2 = 4^(d-4) (z (zbar))^(d-3) (u*(ubar))^((d-5)/2) v^(d-3) (vbar)^((d-4)/2) (w)^((d-4)/2) (wbar)^((d-4)/2) (x)^((d-4)/2) (xbar)^((d-4)/2) /. d-> 4-2\[Epsilon]// Simplify;


kernC =(s34^-\[Epsilon]-(s23+s24+s34)^-\[Epsilon])/((s23 \[Epsilon]+s24 \[Epsilon])s34^2) gdTH2 /. s24 -> zbar-s14-s34 /. s13-> z-s12-s23 /. fullcovariablesTH // Simplify


kernC123cyclicpart1 =s14^-\[Epsilon]/((s12 \[Epsilon]+s34 \[Epsilon])s14^2) gdTH2 /. s24 -> zbar-s14-s34 /. s13-> z-s12-s23  /. 
fullcovariablesTH


kernC123cyclicpart2 =-(s12+s34+s14)^-\[Epsilon]/((s12 \[Epsilon]+s34 \[Epsilon])s14^2) gdTH2 /. s24 -> zbar-s14-s34 /. s13-> z-s12-s23  /. 
fullcovariablesTH// Simplify


ICcycp1=Integrate[kernC123cyclicpart1 /. barback,{u,0,1}]


ICcycp12=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{u,v,w,x,z,\[Epsilon],mb2},Reals]},Integrate[(4^-\[Epsilon] Sqrt[\[Pi]] (1-v)^-\[Epsilon] v^(-2 \[Epsilon]) (-(-1+w) w)^-\[Epsilon] (-(-1+x) x)^-\[Epsilon] (-v x (-1+z))^(-1-\[Epsilon]) z (-(-1+z) z)^(-2 \[Epsilon]) Gamma[1/2-\[Epsilon]])/(x (1-z+v (-1+z+w z)) \[Epsilon] Gamma[1-\[Epsilon]]),{v,0,1}]]


ICcycp13 = Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{u,v,w,x,z,\[Epsilon],mb2},Reals]},Integrate[(4^-\[Epsilon] Sqrt[\[Pi]] x^(-2 (1+\[Epsilon])) (-(-1+w) w (-1+x) (-1+z))^-\[Epsilon] z (-(-1+z) z)^(-2 \[Epsilon]) Gamma[1/2-\[Epsilon]] Gamma[-3 \[Epsilon]] Hypergeometric2F1Regularized[1,-3 \[Epsilon],1-4 \[Epsilon],1+(w z)/(-1+z)])/((-1+z)^2 \[Epsilon]),{x,0,1}]]


ICcycp14 = Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{u,v,w,x,z,\[Epsilon],mb2},Reals]},Integrate[(4^-\[Epsilon] Sqrt[\[Pi]] ((-1+w) w (-1+z))^-\[Epsilon] z (-(-1+z) z)^(-2 \[Epsilon]) Gamma[-1-2 \[Epsilon]] Gamma[1/2-\[Epsilon]] Gamma[1-\[Epsilon]] Hypergeometric2F1Regularized[1,-3 \[Epsilon],1-4 \[Epsilon],1+(w z)/(-1+z)])/((-1+z)^2 \[Epsilon]),{w,0,1}]]


(*  Mellin-Barnes? *)


ICcycp2=Integrate[kernC123cyclicpart2 /. barback,{u,0,1}]


Collect[1-z+v (-1+x+z+w z-x z),x,Simplify]


ICcycp22=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{u,v,w,x,z,\[Epsilon],mb2,a,b},Reals]},Integrate[ (4^-\[Epsilon] Sqrt[\[Pi]] (1-v)^-\[Epsilon] v^(-1-2 \[Epsilon]) (-(-1+w) w)^-\[Epsilon] (1-x)^-\[Epsilon] x^(-2-\[Epsilon]) z (-(-1+z) z)^(-2 \[Epsilon]) (1-z+v (-1+z+w z)+x (v-v z))^-\[Epsilon] Gamma[1/2-\[Epsilon]])/((-1+z) (1-z+v (-1+z+w z)) \[Epsilon] Gamma[1-\[Epsilon]]),{x,0,1}]]


(* ::Section::Closed:: *)
(*Erstes Integral B0 nach Reduktion*)


factorB=Refine[Integrate[(-x(1-x))^-\[Epsilon],{x,0,1}],0<\[Epsilon]<1];
faktorB1 = ((-8+3 d) (-18+5 d) (-16+5 d) (-14+5 d))/((-6+d) (-4+d)^2 (-14+3 d)  pb^6)*factorB (* vorfaktor aus reduktion und vorfaktor aus feynman parameter integral*);
IntB1 = 1/((k1+p2)^2 (k1+p1+p2-pb)^2);


barback ={zbar->1-z,xbar->1-x,vbar->1-v,wbar->1-w,ubar->1-u};
fullcovariablesTH = {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2/Sqrt[vbar w wbar x xbar]) z};
gdTH2 = 4^(d-4) (z (zbar))^(d-3) (u*(ubar))^((d-5)/2) v^(d-3) (vbar)^((d-4)/2) (w)^((d-4)/2) (wbar)^((d-4)/2) (x)^((d-4)/2) (xbar)^((d-4)/2) /. d-> 4-2\[Epsilon]// Simplify;


kernB1=(s23+s24+s34)^-\[Epsilon] gdTH2 /. s24 -> zbar-s14-s34 /. s13-> z-s12-s23 /. fullcovariablesTH /. barback// Simplify;


kernB1cyc=(s12+s14+s24)^-\[Epsilon] gdTH2 /. s24 -> zbar-s14-s34 /. s13-> z-s12-s23 /. fullcovariablesTH /. barback// Simplify;


Ichange1=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,Element[{u,v,w,x,z,\[Epsilon],mb2},Reals],0<\[Epsilon]<1/2},Integrate[kernB1cyc /. barback,{u,0,1}]]


Ichange2=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,Element[{u,v,w,x,z,\[Epsilon],mb2},Reals],0<\[Epsilon]<1/2},Integrate[Ichange1  /. xbar-> 1-x,{x,0,1}]]


Ichange3=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,Element[{u,v,w,x,z,\[Epsilon],mb2},Reals],0<\[Epsilon]<1/2,0<\[Delta]<1},Integrate[Ichange2 ,{v,0,1}]]


I3ersetzt=-((\[Pi] (-(-1+z) z)^(1-2 \[Epsilon]) Gamma[2-3 \[Epsilon]] Gamma[1-\[Epsilon]])/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]])) (Gamma[1-\[Epsilon]]Gamma[1-\[Epsilon]]Hypergeometric2F1[\[Epsilon],1-\[Epsilon],2-2\[Epsilon],z])/Gamma[2-2\[Epsilon]]


(* ((1-z) z)^(1-2 \[Epsilon])  Hypergeometric2F1[\[Epsilon],1-\[Epsilon],2-2 \[Epsilon],z] = (Gamma[2-2\[Epsilon]]Gamma[2-2\[Epsilon]])/Gamma[4-4\[Epsilon]] Hypergeometric3F2[\[Epsilon],1-\[Epsilon],2-2 \[Epsilon],2-2\[Epsilon],4-4\[Epsilon],1] *)


I4ersetzt=-((\[Pi]  Gamma[2-3 \[Epsilon]] (Gamma[1-\[Epsilon]]^3) )/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]] Gamma[2-2 \[Epsilon]])) (Gamma[2-2\[Epsilon]]Gamma[2-2\[Epsilon]])/Gamma[4-4\[Epsilon]] HypergeometricPFQ[{\[Epsilon],1-\[Epsilon],2-2 \[Epsilon]},{2-2\[Epsilon],4-4\[Epsilon]},\[Delta]]


B1=I4ersetzt


(* ::Section::Closed:: *)
(*Zweites Integral B0 nach Reduktion*)


factorB2= (8 (-3+d) (-7+2 d) (-18+5 d) (-16+5 d) (-14+5 d))/(3 (-5+d) (-4+d)^2 (-14+3 d) (-10+3 d) pb^6)*factorB (* vorfaktor aus reduktion und vorfaktor aus feynman parameter integral*);
IntB2 =1/(k1^2 (k1+p1+p2-pb)^2);
kernB2= (s34)^-\[Epsilon]  gdTH2 /. s24 -> 1-E\[Gamma]-s14-s34 /. s13-> E\[Gamma]-s12-s23 ;


kernB2cyc= (s14)^-\[Epsilon]  gdTH2  /. s24 -> zbar-s14-s34 /. s13-> z-s12-s23 /. fullcovariablesTH /. barback// Simplify


I1B2=Assuming[{0<s23<1,0<s24<1,0<s34<1,s24+s34<1,Element[{s12,s23,s24,,s13,s14,s34,\[Epsilon]},Reals],\[Epsilon]>0},intPS[kernB2cyc /. barback,{u,0,1}]]


I2B2=Assuming[{0<s23<1,0<s24<1,0<s34<1,s24+s34<1,Element[{s12,s23,s24,,s13,s14,s34},Reals],\[Epsilon]>0},intPS[I1B2,{x,0,1}]]


I3B2 = intPS[I2B2,{w,0,1}]


I4B2=Refine[intPS[I3B2,{v,0,1}],0<\[Epsilon]<1/2]


I5B2 = Refine[intPS[I4B2,{z,0,\[Delta]}] /. betarep,\[Epsilon]<1/2]


B2=-((\[Pi] \[Delta]^(2-2 \[Epsilon]) Gamma[1-2 \[Epsilon]] Gamma[2-2 \[Epsilon]] Gamma[1-\[Epsilon]]^2 Hypergeometric2F1[2-2 \[Epsilon],-1+3 \[Epsilon],3-2 \[Epsilon],\[Delta]])/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]] Gamma[3-2 \[Epsilon]]))


(* ::Subsubsection:: *)
(*Check of R8 in hep-ph/0311276*)


kaellen[a_,b_,c_]:=a^2+b^2+c^2-2(a*b+a*c+b*c)


(* (4.6) *)
phrep={s23-> (1-y134)*q^2*z1, s24-> (1-y134)*q^2*z2, s12 -> (1-y134)*q^2*(1-z1-z2), s13->q^2*y13, s14 -> q^2 y14, s34 -> q^2*y34};
varrep={y14-> y134*(1-z1)*v, z2->(1-z1)*t, y34-> y134-y13-y14};


1/(s34 s14 s23 s12) /. phrep //. varrep // Simplify


kernelR8 = (1-y134)^(-1-2\[Epsilon])*y134^(1-2\[Epsilon]) (1-z1)^(1-2\[Epsilon]) z1^-\[Epsilon] t^-\[Epsilon] (1-t)^-\[Epsilon] v^-\[Epsilon] (1-v)^-\[Epsilon] * 1/(s13 s14 s23 s24)


Refine[Integrate[(x(1-x))^(-1/2-\[Epsilon])*((ap-am)x+am)^-2,{x,0,1}],{ap>am>0,0<\[Epsilon]<1/2}]


gd4= Collect[-kaellen[y12(y134-y13-y14),y13 z2,y14 z1] /.phrep //.varrep // Simplify,y13,Simplify]


Solve[gd4==0,y13] /. y12 ->  (1-y134)*(1-z1-z2) // Simplify


Integrate[(1-z)^(1-3\[Epsilon]-s) z^(1-2\[Epsilon]+s),{z,0,\[Delta]}]


<<MB.m


?Beta


(Beta[\[Delta],2+s-2 ep,2-s-3 ep] /. betarep)


betarep = {Beta[z_,a_,b_]->Gamma[a]z^a Hypergeometric2F1[a,1-b,a+1,z]/Gamma[a+1]};


int=1/(I*2 Pi) (Beta[\[Delta],2+s-2 ep,2-s-3 ep] /. betarep) (Gamma[2-2ep]Gamma[s+ep]Gamma[1-ep+s]Gamma[-s])/(Gamma[ep]Gamma[1-ep]Gamma[2-2ep+s])


rules = MBoptimizedRules[int, ep -> 0, {}, {\[Delta],ep}]


cont = MBcontinue[int, ep -> 0, rules]


prefB1=-((\[Pi]  Gamma[2-3 \[Epsilon]] (Gamma[1-\[Epsilon]]^3) )/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]] Gamma[2-2 \[Epsilon]]));


MBexpand[cont, Exp[ep EulerGamma], {ep, 0, 1}]


Series[(\[Pi]  Gamma[2-3 \[Epsilon]] (Gamma[1-\[Epsilon]]^3) )/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]] Gamma[2-2 \[Epsilon]]) (-((I \[Delta]^2)/(4 \[Pi]))+(I \[Delta]^3)/(6 \[Pi])),{\[Epsilon],0,0}] /. \[Delta]-> 0.3


SeriesData[\[Epsilon], 0, {Rational[1, 4] Pi \[Delta]^2 + Rational[-1, 6] Pi \[Delta]^3}, 0, 1, 1]


Series[-((4 \[Pi] \[Epsilon] (1+2 \[Epsilon]) (\[Delta]^(2-3 \[Epsilon]) Gamma[2-3\[Epsilon]] Hypergeometric2F1[2-3 \[Epsilon],2+2 \[Epsilon],3-3 \[Epsilon],\[Delta]])/Gamma[3-3\[Epsilon]] Gamma[-\[Epsilon]]^2 Gamma[-2 (1+\[Epsilon])])/((1+\[Epsilon] (-5+6 \[Epsilon])) Gamma[-4 \[Epsilon]])),{\[Epsilon],0,0}] 


serc=Series[-yintcoeffC2 (4 \[Pi] \[Delta]^(2-3 \[Epsilon]) \[Epsilon] (1+2 \[Epsilon]) Gamma[2-3 \[Epsilon]] Gamma[-\[Epsilon]]^2 Gamma[-2 (1+\[Epsilon])] HypExp[Hypergeometric2F1[2-3 \[Epsilon],2+2 \[Epsilon],3-3 \[Epsilon],\[Delta]],\[Epsilon],2])/((1+\[Epsilon] (-5+6 \[Epsilon])) Gamma[3-3 \[Epsilon]] Gamma[-4 \[Epsilon]]),{\[Epsilon],0,-1}]


HypExp[Hypergeometric2F1[\[Epsilon],1-2\[Epsilon],2(1-2\[Epsilon]),z],\[Epsilon],2]


serb1=Series[faktorB1*-((\[Pi] Gamma[2-3 \[Epsilon]] Gamma[2-2 \[Epsilon]] Gamma[1-\[Epsilon]]^3 HypExp[Hypergeometric2F1[1-\[Epsilon],\[Epsilon],4-4 \[Epsilon],\[Delta]],\[Epsilon],2])/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]] Gamma[4-4 \[Epsilon]])) /. d-> 4-2\[Epsilon],{\[Epsilon],0,-1}] /. pb-> 1


serb2=Series[factorB2*-((\[Pi] \[Delta]^(2-2 \[Epsilon]) Gamma[1-2 \[Epsilon]] Gamma[2-2 \[Epsilon]] Gamma[1-\[Epsilon]]^2 HypExp[Hypergeometric2F1[2-2 \[Epsilon],-1+3 \[Epsilon],3-2 \[Epsilon],\[Delta]],\[Epsilon],2])/((-1+2 \[Epsilon]) Gamma[3-4 \[Epsilon]] Gamma[3-2 \[Epsilon]])) /. d-> 4-2\[Epsilon],{\[Epsilon],0,-1}] /. pb-> 1


serc  


+serb1+serb2  // Simplify


<<HypExp`


Integrate[HypExp[HypergeometricPFQ[{2-2 \[Epsilon],-1+3 \[Epsilon],\[Epsilon]},{3-2 \[Epsilon],2\[Epsilon]},z/(1-z)],\[Epsilon],1],{z,0,\[Delta]}]


(* ::Section::Closed:: *)
(*B0 vortrag*)


(* ::Subsubsection:: *)
(**)


Integrate[(p234*x*(1-x))^-\[Epsilon],{x,0,1}]


kernB0v= s13*s24/s34 *p234^-\[Epsilon]  /. p234-> (s23+s24+s34)


kernB0vcyc= s12*s34/s14 *p134^-\[Epsilon]  /. p134-> (s13+s34+s14)


kernB0vAcyc= s23*s14/s24 *p124^-\[Epsilon]  /. p124-> (s12+s14+s24)


fullcovariablesTH


kernB0v1=kernB0vAcyc*gdTH2  /. s24 -> zbar-s14-s34 /. s13-> z-s23-s12 /.
 {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2/Sqrt[vbar w wbar x xbar]) z} /. barback //Simplify 


kernB0vAcyc*gdTH2  /. s24 -> zbar-s14-s34 /. s13-> z-s23-s12 /.
 {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->u*adiff +am} // Simplify


I1Bv=Assuming[{0<s23<1,0<s24<1,0<s34<1,s24+s34<1,Element[{s12,s23,s24,,s13,s14,s34,\[Epsilon]},Reals],\[Epsilon]>0},intPScov[kernB0v1/. barback,{u,0,1}]]


allu=Assuming[{0<s23<1,0<s24<1,0<s34<1,s24+s34<1,Element[{s12,s23,s24,,s13,s14,s34,\[Epsilon]},Reals],\[Epsilon]>0},intPScov[%75/. ubar -> 1-u,{u,0,1}]]


(* ::Subsection::Closed:: *)
(*adiff-part*)


4 z Sqrt[vbar w wbar x xbar]Coefficient[allu[[1]],adiff] /. vbar -> 1-v // Simplify


adiffv=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,0<\[Epsilon]<1/2},intPScov[4 Sqrt[vbar w wbar x xbar]Coefficient[allu[[1]],adiff] /. vbar -> 1-v,{v,0,1}]]


adiffx=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{s12,s23,s24,,s13,s14,s34,\[Epsilon]},Reals],\[Epsilon]>0},intPScov[adiffv /. xbar -> 1-x,{x,0,1}]]


adiffw = PowerExpand[ adiffx ] //. hypergeorule //. hyper2f1fractoz //. hypgeorotate


adifffinal=Assuming[{0<z<1,\[Epsilon]<1/2},intPScov[adiffw,{z,0,\[Delta]}]]


(* ::Subsection:: *)
(*am-part*)


(* ::Subsubsection:: *)
(*vbarwx-part*)


vbarwxv=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2},intPScov[vbar w x z*Coefficient[allu[[1]],am] /. vbar -> 1-v,{v,0,1}]]


vbarwxx=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2},intPScov[vbarwxv /. xbar -> 1-x,{x,0,1}]]


vbarwxw=PowerExpand[vbarwxx[[1]] //. hypergeorule ]//. hyper2f1fractoz //. hypgeorotate


vbarwxfinal=Assuming[{0<z<1},intPScov[ vbarwxw,{z,0,\[Delta]}]]


(* ::Subsubsection:: *)
(*wbar xbar- part*)


wbarxbarv=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,\[Epsilon]>0},intPScov[xbar wbar z*Coefficient[allu[[1]],am] /. vbar -> 1-v,{v,0,1}]]


wbarxbarx=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2},intPScov[wbarxbarv/. xbar -> 1-x,{x,0,1}]]


wbarxbarw=PowerExpand[wbarxbarx] //. hypergeorule //. hyper2f1fractoz //. hypgeorotate


wbarxbarfinal = Assuming[{0<z<1},intPScov[ wbarxbarw,{z,0,\[Delta]}]]


(* ::Subsubsection:: *)
(*root-part*)


rootv=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{s12,s23,s24,,s13,s14,s34,\[Epsilon]},Reals],\[Epsilon]>0},intPScov[-2*z*Sqrt[vbar*w*wbar*x*xbar]^-1*Coefficient[allu[[1]],am] /. vbar -> 1-v,{v,0,1}]]


rootx=Assuming[{0<x<1,0<w<1,0<v<1,0<z<1,\[Epsilon]<1/2,Element[{s12,s23,s24,,s13,s14,s34,\[Epsilon]},Reals]},intPScov[rootv /. xbar -> 1-x,{x,0,1}]]


rootw=PowerExpand[rootx] //. hypergeorule //. hyper2f1fractoz 


rootfinal=Assuming[{0<z<1},intPScov[ rootw,{z,0,\[Delta]}]]


(* ::InheritFromParent:: *)
(**)


allnew = -((2^(-1-2 \[Epsilon]) (asum) Sqrt[\[Pi]] v^(2-2 \[Epsilon]) vbar^-\[Epsilon] w^-\[Epsilon] wbar^-\[Epsilon] x^(1-\[Epsilon]) xbar^-\[Epsilon] z zbar (z zbar)^(-2 \[Epsilon]) (v w z+zbar-vbar zbar)^-\[Epsilon] Gamma[1/2-\[Epsilon]])/((-1+vbar+v x) Gamma[1-\[Epsilon]])) /. xbar->1-x /. vbar->1-v //Simplify;


barback


arep


allnew /. arep //PowerExpand


kernohneasum=(2^(-2 \[Epsilon]) Sqrt[\[Pi]] (1-v)^-\[Epsilon] v^(1-3 \[Epsilon]) w^-\[Epsilon] wbar^-\[Epsilon] (1-x)^(-1-\[Epsilon]) x^(1-\[Epsilon]) z^(1-2 \[Epsilon]) zbar^(1-2 \[Epsilon]) (w z+zbar)^-\[Epsilon] Gamma[1/2-\[Epsilon]])/Gamma[1-\[Epsilon]];


arep = {asum -> 2(z-2 w z zbar+v w z zbar-v x z zbar+2 v w x z zbar-v^2 w x z zbar)}


$GenerateConditions=False


newv=Integrate[allnew /. arep /. xbar->1-x /. vbar -> 1-v,{v,0,1},GenerateConditions->False]


newx=Integrate[PowerExpand[newv],{x,0,1},GenerateConditions->False]


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,1]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz 


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,2]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,3]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,4]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,5]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,6]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz


(* alternative from own calculation*)
arepalt=-2*z*(-wbar xbar-w x vbar)// Expand;
Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arepalt][[1]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz 
Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arepalt][[2]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] //. hypergeorule //. hyper2f1fractoz


4^-\[Epsilon]/. d-> 4-2\[Epsilon] /. \[Epsilon]-> -0.1


Pi^(4-3d)*8*Pi^((3d-6)/2)/. d-> 4-2\[Epsilon] /. \[Epsilon]->- 0.1


%563*Gamma[\[Epsilon]]Gamma[1-\[Epsilon]]^2/Gamma[2-2\[Epsilon]]/. \[Epsilon]-> -0.1 /. z-> 0.3


(* ::InheritFromParent:: *)
(**)


(* ::InheritFromParent:: *)
(*-0.29687977219451267/(-0.4729594604232403`)*)


(* ::InheritFromParent:: *)
(*-0.913701987403392I/(-0.6509728504423495` I)*)


(* ::Section::Closed:: *)
(*root of the gram*)


(zbar-s34)^2 (ap-s23)(s23-am) /. deltas /. {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->(ap-am)u+am} // FullSimplify


del4 = s12^2 s34^2+s13^2 s24^2+s14^2 s23^2-2 s12 s34 s13 s24-2s12 s34 s14 s23-2s13 s24 s14 s23


del4sub = del4 /. s24 -> zbar -s14-s34 /. s13 -> z-s12-s23


Solve[-del4sub==0,s23] // Simplify // Factor


rootp=(s12 s14 s34+s14 s34 z+s34^2 z+s12 s14 zbar+s12 s34 zbar-s14 z zbar-2 s34 z zbar-s12 zbar^2+z zbar^2+2 Sqrt[s12 s14 s34 (s14+s34-zbar) (s34 z+s12 zbar-z zbar)])/(s34-zbar)^2;
rootm=(s12 s14 s34+s14 s34 z+s34^2 z+s12 s14 zbar+s12 s34 zbar-s14 z zbar-2 s34 z zbar-s12 zbar^2+z zbar^2-2 Sqrt[s12 s14 s34 (s14+s34-zbar) (s34 z+s12 zbar-z zbar)])/(s34-zbar)^2;


Simplify[rootm+rootp]


% /. s24 -> zbar-s14-s34 /. s13-> z-s23-s12 /.
 {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->u*adiff +am} /. vbar -> 1-v// Factor 


-2 (-1+w+x-2 w x+v w x) z-(-2 z(-wbar xbar-w x vbar) /. barback )// Simplify


(* ::InheritFromParent:: *)
(**)


% /. s24 -> zbar-s14-s34 /. s13-> z-s23-s12 /.
 {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->u*adiff +am} /. vbar -> 1-v// Simplify


(2 (z (s34-zbar) (s14+s34-zbar)+s12 (s34-zbar) zbar+s12 s14 (s34+zbar)))/(s34-zbar)^2 /. s24 -> zbar-s14-s34 /. {s13-> z-s23-s12 s12->v w z,s34->vbar zbar,s14->v x zbar,s23->u*adiff +am} //Expand


{wbar->1-w,(1-w)^a2_ w^a1_ (w c1_+c2_)^a3_->(-1)^a3 b^a3 Hypergeometric2F1[-a3,a1+1,2+a1+a2,-(a/b)]}


Expand[PowerExpand[Integrate[PowerExpand[(Integrate[Expand[arep][[1,2,4]]*kernohneasum /. xbar->1-x /. vbar -> 1-v,{v,0,1}])[[1]]],{x,0,1}]]] 


%777 //. {wbar->1-w,(1-w)^a2_ w^a1_ (w c1_+c2_)^a3_:> (-1)^a3 c2^a3 Hypergeometric2F1[-a3,a1+1,2+a1+a2,-(c1/c2)]}


%777 //. hypergeorule


(* ::Section::Closed:: *)
(*new Kernel B0 V2*)


barback ={zbar->1-z,xbar->1-x,vbar->1-v,wbar->1-w,ubar->1-u};
(* Typo in Paper for change of variables! *)
fullcovariablesTH = {s12->v w z,s34->vbar zbar,s14->v x zbar,s23->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2*Sqrt[vbar w wbar x xbar]) z};
fullcovariablesTH2 = {s12->v w z,s34->vbar zbar,s14->v x zbar,s23-> u adiff + am};
hyper2f1fractoz = {zbar->1-z,(-1+z)^a_->(1-z)^a*(-1)^a,Hypergeometric2F1[a_,b_,c_,-(z/(1-z))]->(1-z)^b Hypergeometric2F1[c-a,b,c,z]};
hypergeorule = {wbar->1-w,(-1+w)^a_->(1-w)^a*(-1)^a,(1-w)^a2_ w^a1_ (w a_+b_)^a3_->(-1)^a3 b^a3 Hypergeometric2F1[1+a1,-a3,2+a1+a2,-(a/b)]};
hypergeo1= {Hypergeometric2F1Regularized[3/2-\[Epsilon],\[Epsilon],2-\[Epsilon],1] ->Hypergeometric2F1[3/2-\[Epsilon],\[Epsilon],2-\[Epsilon],1]/Gamma[2-\[Epsilon]],Hypergeometric2F1[a_,b_,c_,1]->(Gamma[c]Gamma[c-a-b])/(Gamma[a-c]Gamma[c-b])};
SetOptions[Integrate,GenerateConditions->False];
gdTH2 = 4^(d-4) (z (zbar))^(d-3) (u*(ubar))^((d-5)/2) v^(d-3) (vbar)^((d-4)/2) (w)^((d-4)/2) (wbar)^((d-4)/2) (x)^((d-4)/2) (xbar)^((d-4)/2) /. d-> 4-2\[Epsilon]// Simplify;
(* anticyclic 3 \[Rule] 2 \[Rule] 1 \[Rule] 3 *)
acyc = {s12->s13,s13->s23,s14->s34,s23->s12,s34->s24,s24->s14};


K=(s13*s24)/s34*((k.p1)(k.p3))/(k^2 (k+p2+p3+p4)^2);


(* after PaVe *)
K1 = ((s13*s24)/s34)*(1/(16(dim-1))) (dim*(s23+s34)*(s12+s13+s14)-2 s13*(s23+s24+s34))*I*((Gamma[\[Epsilon]]Gamma[1-\[Epsilon]]^2)/Gamma[2-2\[Epsilon]])*((-p234^2)^-\[Epsilon]) 


(s13*s24)/s34*(D*(s23+s34)*(s12+s13+s14)-2 s13*(s23+s24+s34)) /(16(dim-1)k^2 (k-p2-p3-p4)^2)  /. D->1 // Expand


barback


(* Integration over u,v and x *)
intUVX[intlist_,n_]:=Factor[ExpandAll[
Integrate[
Expand[
PowerExpand[Integrate[
Expand[
PowerExpand[
Integrate[
Expand[intlist][[n]]*gdTH2 /.{xbar->1-x,vbar->1-v,ubar->1-u},{u,0,1}]
]],{v,0,1},GenerateConditions->False]]],{x,0,1}]]]


intlist=List@@Plus[Expand[K1 /. p234^2 -> (s23+s24+s34)  /. acyc /. { s24 -> zbar-s14-s34, s13-> z-s12-s23}  /. fullcovariablesTH ]];


inttableeval=Table[intUVX[intlist,i],{i,Length[intlist]}]


hyper2f1fractoz


inttable3=inttableeval //. hypergeorule //. hyper2f1fractoz  //. hypergeo1


Export["B0v2.m",Collect[Plus@@inttable3,Hypergeometric2F1[a_,b_,c_,d_]]]


Union[inttable3 /. a_ Hypergeometric2F1[a1_,a2_,a3_,a4_]->Hypergeometric2F1[a1,a2,a3,a4]]


hypbplus=Hypergeometric2F1[a_,b_,c_,z_]->(2b-c+2+(a-b-1)z)/(b-c+1) Hypergeometric2F1[a,b+1,c,z]+((b+1)(z-1))/(b-c+1) Hypergeometric2F1[a,b+2,c,z];


hypbminus=Hypergeometric2F1[a_,b_,c_,z_]->(c-2b+2+(b-a-1)z)/((b-1)(z-1)) Hypergeometric2F1[a,b-1,c,z]+(b-c-1)/((b-1)(z-1)) Hypergeometric2F1[a,b-2,c,z];


hypcplus=Hypergeometric2F1[a_,b_,c_,z_]->((2c-a-b+1)z-c)/(c(z-1)) Hypergeometric2F1[a,b,c+1,z]+((a-c-1)(c-b+1))/(c(c+1)(z-1)) Hypergeometric2F1[a,b,c+2,z];


hypcminus=Hypergeometric2F1[a_,b_,c_,z_]->((c-1)(2-c-(a+b-2c+3)z))/((a-c+1)(b-c+1)z) Hypergeometric2F1[a,b,c-1,z]+((c-1)(c-2)(1-z))/((a-c+1)(b-c+1)z) Hypergeometric2F1[a,b,c-2,z];


(* ::Section::Closed:: *)
(*Treelevel Integration*)


Dcoeffreplace = {
(a0_+a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a5_*d^5+a6_*d^6+a7_*d^7):> Dcoeff[a0,a1,a2,a3,a4,a5,a6,a7],
(a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a5_*d^5+a6_*d^6+a7_*d^7):> Dcoeff[0,a1,a2,a3,a4,a5,a6,a7],
(a0_+a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a5_*d^5+a6_*d^6):> Dcoeff[a0,a1,a2,a3,a4,a5,a6,0],
(a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a5_*d^5+a6_*d^6):> Dcoeff[0,a1,a2,a3,a4,a5,a6,0] ,
(a0_+a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a6_*d^6):>Dcoeff[a0,a1,a2,a3,a4,0,a6,0] , 
(a0_+a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a5_*d^5):> Dcoeff[a0,a1,a2,a3,a4,a5,0,0],
(a1_*d+a2_*d^2+a3_*d^3+a4_*d^4+a5_*d^5):> Dcoeff[0,a1,a2,a3,a4,a5,0,0], 
(a0_+a1_*d+a2_*d^2+a3_*d^3+a4_*d^4):> Dcoeff[a0,a1,a2,a3,a4,0,0,0]};


diags=List@@Plus[Total[Import["/home/users/moos/BSGamma/lm/TreeBSG4BodyLS_O1O1uu.m"]] /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ];


srep={s12->s[12],s13->s[13],s14->s[14],s23->s[23],s24->s[24],s34->s[34]};


diagsshort=List@@Plus[Collect[Total[diags] ,{s12,s13,s14,s23,s34,s24,Den[_]}]/.Dcoeffreplace /.denoms //Expand];


testdiagskernels=gdTH2*diagsshort /. s24 -> zbar -s14-s34 /. s13 -> z-s12-s23 /. fullcovariablesTH; 


hypergeoruleu = {ubar->1-u,(1-u)^a2_ u^a1_ (u a_+b_)^a3_->(-1)^a3 b^a3 Hypergeometric2F1[1+a1,-a3,2+a1+a2,-(a/b)]};
betaruleu = { ubar -> 1-u ,(1-u)^a2_ u^a1_->Beta[1+a1,1+a2]};
hypergeorulev = {(-1+v)^a_->(-1)^a (1-v)^a,vbar->1-v,(1-v)^a2_ v^a1_ (v a_+b_)^a3_->(-1)^a3 b^a3 Hypergeometric2F1[1+a1,-a3,2+a1+a2,-(a/b)]};
betarulev = { vbar -> 1-v ,(1-v)^a2_ v^a1_->Beta[1+a1,1+a2]};
hypergeorulex = {(-1+x)^a_->(-1)^a (1-x)^a,xbar->1-x,(1-x)^a2_ x^a1_ (x a_+b_)^a3_->(-1)^a3 b^a3 Hypergeometric2F1[1+a1,-a3,2+a1+a2,-(a/b)]};
betarulex = { (-1+x)^a_->(-1)^a (1-x)^a,xbar -> 1-x ,(1-x)^a2_ x^a1_->Beta[1+a1,1+a2]};
hypergeorulew = {(-1+w)^a_->(-1)^a (1-w)^a,wbar->1-w,(1-w)^a2_ w^a1_ (w a_+b_)^a3_->(-1)^a3 b^a3 Hypergeometric2F1[1+a1,-a3,2+a1+a2,-(a/b)]};
betarulew = { (-1+w)^a_->(-1)^a (1-w)^a,wbar -> 1-w ,(1-w)^a2_ w^a1_->Beta[1+a1,1+a2]};


newu2=Expand[PowerExpand[testdiagskernels]] //. barback //. hypergeoruleu //. betaruleu // Simplify


newv2 = List@@Plus[Expand[Total[newu2]]]  //. hypergeorulev //. betarulev // PowerExpand


newx2 = Total[newv2] //. hypergeorulex //. betarulex


neww2 = List@@Plus[PowerExpand[Expand[Total[newx2]]]] //. hypergeorulew //. betarulew


finz = Total[Integrate[neww2,z]]


totaltree2=(finz /. z->1)-(finz /. z->\[Delta])


Export["PSIntegratedTreeDiagramsV2.m",totaltree2]


<<HypExp`;


fnoexp=Import["PSIntegratedTreeDiagramsV2.m"];


fexp=  fnoexp /. Hypergeometric2F1[a___]:>  HypExp[Hypergeometric2F1[a],\[Epsilon],1]


Export["PSIntegratedTreeDiagramsV2OrderZero.m",%5];


Import["PSIntegratedTreeDiagramsV2OrderZero.m"]


Series[fexp,{\[Epsilon],0,0}]





(* ::Section:: *)
(*One-Loop Integration*)


(* ::Input:: *)
(**)


denrep={"den(p1-q4)"->"Den[p1-q4]","den(q1+q4)"->"Den[q1+q4]","den(-q2-q4)"->"Den[-q2-q4]","den(q3+q4)"->"Den[q3+q4]" ,"den(q1+k1)"->"Den[q1+k1]","den(-p1+k1)"->"Den[-p1+k1]","den(-q2+k1)"->"Den[-q2+k1]","den(k1)"->"Den[k1]","den(-k1)"->"Den[-k1]",
"den(p1-q4-k1)"->"Den[-k1+p1-q4]","den(k1+q1+q4)"->"Den[k1+q1+q4]" ,"den(p1-k1)"->"Den[p1-k1]","den(p1+k1)"->"Den[p1+k1]","den(q1-k1)"->"Den[q1-k1]","den(q2-k1)"->"Den[q2-k1]","den(q2+k1)"->"Den[q2+k1]","den(-q2-k1)"->"Den[-q2-k1]",
"den(q3-k1)"->"Den[q3-k1]","den(q3+k1)"->"Den[q3+k1]","den(q4-k1)"->"Den[q4-k1]","den(-q4+k1)"->"Den[-q4+k1]","den(q3+q4+k1)"->"Den[q3+q4+k1]","den(q3+q4-k1)"->"Den[q3+q4-k1]","den(q1+q4+k1)"->" Den[q1+q4+k1]",
"den(-q2-q4-k1)"->"Den[-q2-q4-k1]","den(-q2-q4+k1)"->"Den[-q2-q4+k1]","den(q1+q4-k1)"->"Den[q1+q4-k1]","den(p1-q4+k1)"->"Den[p1-q4+k1]"};
massdenrep={"massden(k1)"->"Den[k1,mb]","massden(-k1)"->"Den[-k1,mb]","massden(p1-q4)"->"Den[p1-q4,mb]","massden(q1+q4)"->"Den[q1+q4,mb]","massden(-q2-q4)"->"Den[-q2-q4,mb]","massden(q3+q4)"->"Den[q3+q4,mb]" ,"massden(q1+k1)"->"Den[q1+k1,mb]","massden(-q2+k1)"->"Den[-q2+k1,mb]",
"massden(p1-q4-k1)"->"Den[-k1+p1-q4,mb]","massden(k1+q1+q4)"->"Den[k1+q1+q4,mb]" ,"massden(p1-k1)"->"Den[p1-k1,mb]","massden(p1+k1)"->"Den[p1+k1,mb]","massden(q1-k1)"->"Den[q1-k1,mb]",
"massden(q2-k1)"->"Den[q2-k1,mb]","massden(-q2-k1)"->"Den[-q2-k1,mb]","massden(q3-k1)"->"Den[q3-k1,mb]","massden(q3+k1)"->"Den[q3+k1,mb]","massden(q4-k1)"->"Den[q4-k1,mb]","massden(-q4+k1)"->"Den[-q4+k1,mb]",
"massden(q3+q4+k1)"->"Den[q3+q4+k1,mb]","massden(q3+q4-k1)"->"Den[q3+q4-k1,mb]","massden(q1+q4+k1)"->" Den[q1+q4+k1,mb]","massden(-q2-q4-k1)"->"Den[-q2-q4-k1,mb]","massden(-q2-q4+k1)"->"Den[-q2-q4+k1,mb]",
"massden(q1+q4-k1)"->"Den[q1+q4-k1,mb]","massden(p1-q4+k1)"->"Den[p1-q4+k1,mb]"};
spnot={sp[p1,p2]->s12/2,sp[p1,p3]-> s13/2,sp[p1,p4]-> s14/2,sp[p2,p3]->s23/2,sp[p2,p4]-> s24/2,sp[p3,p4]-> s34/2};
rul1={"s12"->"1","s13"->"1","s14"->"1","qk1"->"1","qk2"->"1","qk3"->"1","qk4"->"1","s23"->"1","s24"->"1","s34"->"1"};
srep={s12->s[12],s13->s[13],s14->s[14],s23->s[23],s24->s[24],s34->s[34],qk1->s[k1],qk2->s[k2],qk3->s[k3],qk4->s[k4],k2->s[kk],s123->s[123],s1234->s[1234],s1243->s[1243]};
Dcoeffreplace = {(a0_+a1_*d+a2_*d^2+a3_*d^3):> Dcoeff[a0,a1,a2,a3],(a0_+a1_*d+a2_*d^2+d^3):> Dcoeff[a0,a1,a2,1],(a1_*d+a2_*d^2+a3_*d^3):> Dcoeff[0,a1,a2,a3],(a1_*d+a2_*d^2+d^3):> Dcoeff[0,a1,a2,1],
(a0_+a1_*d+a3_*d^3):> Dcoeff[a0,a1,0,a3],(a0_+a1_*d+a2_*d^2):> Dcoeff[a0,a1,a2,0],(a1_*d+a2_*d^2+d^3):> Dcoeff[0,a1,a2,1],(a1_*d+a2_*d^2):> Dcoeff[0,a1,a2,0],
(a1_*d+d^2):> Dcoeff[0,a1,1,0],(a0_+a1_*d):> Dcoeff[a0,a1,0,0],(a0_+d):> Dcoeff[a0,1,0,0],(a0_+a2_*d^2):> Dcoeff[a0,0,a2,0],(a0_+d^2):> Dcoeff[a0,0,1,0],(a1_*d):> Dcoeff[0,a1,0,0]};


(* ::Subsection:: *)
(*Total of diagrams*)


diags=List@@Plus[Total[ToExpression[StringReplace[StringReplace[StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O3O3uu.log"],"\n"]," "],";"],{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]] ] /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ];


diag2proto=Collect[Total[diags] /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}]


diag2=List@@Plus[diag2proto]


diag3=Collect[Expand[diag2] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]}


diag4 = List@@Plus[Total[diag3]]


Export["~/BSGamma/lm/OneLoopBSG4BodyO3O3uu.m",diag4]


Den[q3+q4,k1+q3+q4,k1+q1+q2+q3+q4,-k1,k1+q3,s[k4,k4,13,24]] //. {Den[a___,q3+q4,b___]->1/s34 Den[a,b],Den[a___,q1+q4,b___]->1/s14 Den[a,b],Den[a___,q2+q4,b___]->1/s24 Den[a,b],
Den[a___,q1+q2,b___]->1/s12 Den[a,b],Den[a___,q1+q3,b___]->1/s13 Den[a,b],Den[a___,q2+q3,b___]->1/s23 Den[a,b]} //. {Den[a___,s[b1___,13,b2___]]->s13 Den[a,s[b1,b2]],Den[a___,s[b1___,24,b2___]]->s24 Den[a,s[b1,b2]],
Den[a___,s[b1___,12,b2___]]->s12 Den[a,s[b1,b2]],Den[a___,s[b1___,23,b2___]]->s23 Den[a,s[b1,b2]],
Den[a___,s[b1___,14,b2___]]->s14 Den[a,s[b1,b2]],Den[a___,s[b1___,34,b2___]]->s34 Den[a,s[b1,b2]]}


diag5=diag4  //. 
{Den[a___,q3+q4,b___]->1/s34 Den[a,b],Den[a___,q1+q4,b___]->1/s14 Den[a,b],Den[a___,q2+q4,b___]->1/s24 Den[a,b],
Den[a___,q1+q2,b___]->1/s12 Den[a,b],Den[a___,q1+q3,b___]->1/s13 Den[a,b],Den[a___,q2+q3,b___]->1/s23 Den[a,b]
,Den[a___,q1+q2+q3,b___]->1/(s12+s13+s23) Den[a,b]} //. 
{Den[a___,s[b1___,13,b2___]]->s13 Den[a,s[b1,b2]],Den[a___,s[b1___,24,b2___]]->s24 Den[a,s[b1,b2]],
Den[a___,s[b1___,12,b2___]]->s12 Den[a,s[b1,b2]],Den[a___,s[b1___,23,b2___]]->s23 Den[a,s[b1,b2]],
Den[a___,s[b1___,14,b2___]]->s14 Den[a,s[b1,b2]],Den[a___,s[b1___,34,b2___]]->s34 Den[a,s[b1,b2]]} /. Den[a___,s[]]->Den[a]


diag5 /. Den[a___,k1+q3+q4,b___]->Den[a,b] /. Den[a___,k1+q1+q2+q3+q4,b___]->Den[a,b] /. Den[a___,-k1,b___]->Den[a,b] /. Den[a___,-k1+q1,b___]->Den[a,b] /. 
Den[a___,-k1+q3,b___]->Den[a,b] /. Den[a___,-k1+q2,b___]->Den[a,b] /. Den[a___,k1+q2,b___]->Den[a,b]  //. Den[a___,k1+c_,b___]->Den[a,b] //. Den[a___,-k1+c_,b___]->Den[a,b] /. Den[a___,k1+q3,b___]->Den[a,b] /. Den[a___,k1-q2,b___]->Den[a,b] /. Den[a___,k1+q1,b___]->Den[a,b] /. Den[a___,s[a1___,k1,a2___]]-> Den[a,s[a1,a2]] /.
 Den[a___,s[a1___,k2,a2___]]-> Den[a,s[a1,a2]] /. Den[a___,s[a1___,k3,a2___]]-> Den[a,s[a1,a2]] /. Den[k1,s[kk]]->0 /.  Den[s[k1]]->0 //. Den[k1,s[k4]]-> 0/. Den[a___,s[a1___,k4,a2___]]-> Den[a,s[a1,a2]] /. Den[k1]->0 /. Den[]->0 /. Den[s[]]->0 // Union


(* ::Subsection::Closed:: *)
(*176 stil split O3O3uu (BETTER control over expression than in version before with total)*)


diagslist176=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O3O3uu.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176fin=Collect[Collect[Expand[diag176proto[diagslist176]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO3O3uuBeforeIBP.m",diagslist176fin];


(* ::Subsection::Closed:: *)
(*176 stil split O5O3uu*)


diagslist176O5O3=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O5O3uu.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO5O3=Collect[Collect[Expand[diag176proto[diagslist176O5O3]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO5O3uuBeforeIBP.m",diagslist176finO5O3];


(* ::Subsection::Closed:: *)
(*176 stil split O3O5uu*)


diagslist176O3O5=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O3O5uu.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO3O5=Collect[Collect[Expand[diag176proto[diagslist176O3O5]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO3O5uuBeforeIBP.m",diagslist176finO3O5];


(* ::Subsection::Closed:: *)
(*176 stil split O5O5uu*)


diagslist176O5O5=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O5O5uu.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO5O5=Collect[Collect[Expand[diag176proto[diagslist176O5O5]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO5O5uuBeforeIBP.m",diagslist176finO5O5];


(* ::Subsection::Closed:: *)
(*176 stil split O3O3ss *)


diagslist176O3O3ss=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O3O3ss.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO3O3ssX=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O3O3ss],onetrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


diagslist176finO3O3ssS=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O3O3ss],twotrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO3O3ssBeforeIBP.m",Onetrace*diagslist176finO3O3ssX+Twotrace*diagslist176finO3O3ssS];


(* ::Subsection::Closed:: *)
(*176 stil split O5O3ss*)


diagslist176O5O3ss=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O5O3ss.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO5O3ssX=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O5O3ss],onetrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


diagslist176finO5O3ssS=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O5O3ss],twotrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO5O3ssBeforeIBP.m",Onetrace*diagslist176finO5O3ssX+Twotrace*diagslist176finO5O3ssS];


(* ::Subsection::Closed:: *)
(*176 stil split O3O5ss*)


diagslist176O3O5ss=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O3O5ss.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand 


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO3O5ssX=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O3O5ss],onetrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


diagslist176finO3O5ssS=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O3O5ss],twotrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO3O5BeforeIBP.m",Onetrace*diagslist176finO3O5ssX+Twotrace*diagslist176finO3O5ssS];


(* ::Subsection::Closed:: *)
(*176 stil split O5O5ss*)


diagslist176O5O5ss=ToExpression[
StringReplace[StringReplace[
StringSplit[StringDelete[StringDelete[Import["~/BSGamma/lm/form/OneLoopBSG4BodyNDR_O5O5ss.log"],
"\n"]," "],";"],
{"eps(q1,q2,q3,q4)"->"Eps[q1,q2,q3,q4]"}],denrep]]  /. p1->q1+q2+q3+q4  /. eps1234->0 /. Den[-a_-b_]->Den[a+b] //Expand ;


diag176proto[diag_]:=Collect[diag /. gDen[a_]->Den[a] /. srep //. Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]//. 
Den[a___]*massDen[b___]^3->Den[a,{b,mb},{b,mb},{b,mb}] //. Den[a___]*massDen[b___]^2->Den[a,{b,mb},{b,mb}] //. Den[a___]*massDen[b___]->Den[a,{b,mb}]//.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} //. {Qb-> Q[d],Qs->Q[d],Qd->Q[d],Qu->Q[u]} //.
  {gs^2 Ta^2 Q[u]^2->g[s2t2u2],gs^2 Ta^2 Q[d]^2->g[s2t2d2],gs^2 Ta^2 Q[u]Q[d]->g[s2t2ud]},{Den[a___]*g[b___]}];


diagslist176finO5O5ssX=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O5O5ss],onetrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


diagslist176finO5O5ssS=Collect[Collect[Expand[Coefficient[diag176proto[diagslist176O5O5ss],twotrace]] /. s[a___]*Den[b___]->Den[b,s[a]],Den[a___]*g[b___]] /. {a_ *g[c___] Den[b___] :> (a /. Dcoeffreplace) g[c] Den[b]} /.
Den[b___,s[a___]] :> Den[b]s[a],Den[___]]  //. Den[k1+p1_,rest___,{k1,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{k1-p1,mb},rest2,{k1+p3-p1,mb}] (*//. 
Den[-k1,rest___,{k1+p2_,mb},rest2___,{k1+p3_,mb}] :>    Den[k1,rest,{-k1+p2,mb},rest2,{-k1+p3,mb}] //. { Den[-k1,rest___,{-k1+p3_,mb}] :> Den[k1,rest,{k1+p3,mb}], 
Den[rest1___,-k1,rest2___,k1+p3_,rest3___] :> Den[rest1,k1,rest2,-k1+p3,rest3]}*)


Export["~/BSGamma/lm/Mathematica/All176DiagramsO5O5ssBeforeIBP.m",Onetrace*diagslist176finO5O5ssX+Twotrace*diagslist176finO5O5ssS];


(* ::Section:: *)
(*Change into notation of FIRE*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];


(* ::Subsection::Closed:: *)
(*group28*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=28;
invsg28={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p3+pb)^2},{7,(k1+p2)^2},{8,(k1-p3)^2},{9,(k1-p1)^2},{10,(-p1-p3+pb)^2},{11,(+p2+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g28 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b], 
			(* replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,24,b] ,
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ z* F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
			F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b] + F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
			F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b]  ,
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			(* invariants containing the loop momenta: *)
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																			                      F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1, 
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group28={diagslist176fin[[4*28-3]],diagslist176fin[[4*28-2]],diagslist176fin[[4*28-1]],
diagslist176fin[[4*16-3]],diagslist176fin[[4*16-2]],diagslist176fin[[4*16-1]],
diagslist176fin[[4*33-3]],diagslist176fin[[4*33-2]],diagslist176fin[[4*33-1]],
diagslist176fin[[4*29-3]],diagslist176fin[[4*29-2]],diagslist176fin[[4*29-1]],
diagslist176fin[[4*17-3]],diagslist176fin[[4*17-2]],diagslist176fin[[4*17-1]],
diagslist176fin[[4*38-3]],diagslist176fin[[4*38-2]],diagslist176fin[[4*38-1]]}/.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


exp4fire1group28= tab[group28,repk1g28]


% - (% /. Den[___]->0) /. a_ Den[b___]-> Den[b]


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28.m",exp4fire1group28 /. F[a___]:> F[28,{a}]]


exp4firegroup28total=Total[exp4fire1group28 /. F[a___]:> F[28,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28total.m",exp4firegroup28total]


exp4firegroup28onlyints = Union[List@@Plus[ Expand[Total[exp4fire1group28]] //.
a_ *F[b___]->F[b]]]  /. F[b___]->{28,{b}}


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass28.m",exp4firegroup28onlyints]


(* ::Subsection::Closed:: *)
(*group28s*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=281;
invsg281={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p3+pb)^2},{7,(k1+p2)^2},{8,(k1-p3)^2},{9,(k1-p1)^2},{10,(pb-p1-p3)^2},{11,(pb-p1-p2)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g281 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1+pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,34,b]-s[a,23,b]-s[a,24,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group281={diagslist176fin[[4*28]],
diagslist176fin[[4*16]],
diagslist176fin[[4*33]],
diagslist176fin[[4*29]],
diagslist176fin[[4*17]],
diagslist176fin[[4*44-1]]} /.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule, 
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group281= tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup281total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"total.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"total"]] /. F[a___]:> F[gnum,{a}]


exp4firegroup281onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsection::Closed:: *)
(*group25*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
invsg25={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p2+p3)^2},{7,(k1+p2)^2},{8,(k1+p3)^2},{9,(k1-p1)^2},{10,(pb-p1-p2)^2},{11,(pb-p2-p3)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
Table[invsg25[[i,2]],{i,1,14}]
invsg25 // TableForm


repk1g25 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q2+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]-
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			(* invariants containing the loop momenta *)
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
																							    F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			(* Conditions for the delta-functions *)
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group25={diagslist176fin[[4*25-3]],diagslist176fin[[4*25-2]],diagslist176fin[[4*25]],
diagslist176fin[[4*13-3]],diagslist176fin[[4*13-2]],diagslist176fin[[4*13]],
diagslist176fin[[4*44-3]],diagslist176fin[[4*44-2]],diagslist176fin[[4*44]],
diagslist176fin[[4*26-3]],diagslist176fin[[4*26-2]],diagslist176fin[[4*26]],
diagslist176fin[[4*14-3]],diagslist176fin[[4*14-2]],diagslist176fin[[4*14]],
diagslist176fin[[4*34-3]],diagslist176fin[[4*34-2]],diagslist176fin[[4*34]]} //. 
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1-q3,b___] :> (Den[a,k1-q3,b] /. k1 :>   -k1 ) };


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]]  //. rule] //.rule ] //. rule ] //.rule,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group25=tab[group25,repk1g25]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group25.m",exp4fire1group25 /. F[a___]:> F[25,{a}]]


exp4firegroup25total=Total[exp4fire1group25 /. F[a___]:> F[25,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group25total.m",exp4firegroup25total]


exp4firegroup25onlyints = Union[List@@Plus[ Expand[Total[exp4fire1group25]] //.
a_ *F[b___]->F[b]]]  /. F[b___]->{25,{b}}


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass25.m",exp4firegroup25onlyints]


(* ::Subsection::Closed:: *)
(*group25ubar*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=251;
invsg251={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p2+p3)^2},{7,(k1+p2)^2},{8,(k1+p3)^2},{9,(k1-p1)^2},{10,(pb-p2-p3)^2},{11,(pb-p1-p3)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g251 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q2+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,24,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			(* invariants containing the loop momenta *)
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
																							    F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			(* Conditions for the delta-functions *)
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group251={diagslist176fin[[4*25-1]],
diagslist176fin[[4*13-1]],
diagslist176fin[[4*26-1]],
diagslist176fin[[4*14-1]],
diagslist176fin[[4*34-1]],
diagslist176fin[[4*41-2]]}  //. 
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1-q3,b___] :> (Den[a,k1-q3,b] /. k1 :>   -k1 ) };


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]]  //. rule] //.rule ] //. rule ] //.rule,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group251=tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup251total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"total.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] ]


exp4firegroup251onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsection::Closed:: *)
(*group31*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=31;
invsg31={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p1+p2)^2},{7,(k1+p2)^2},{8,(k1-p3)^2},{9,(k1+p1)^2},{10,(-p1-p2+pb)^2},{11,(+p1+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g31 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group31={diagslist176fin[[4*31-3]],diagslist176fin[[4*31-1]],diagslist176fin[[4*31]],
diagslist176fin[[4*19-3]],diagslist176fin[[4*19-1]],diagslist176fin[[4*19]],
diagslist176fin[[4*41-3]],diagslist176fin[[4*41-1]],diagslist176fin[[4*41]],
diagslist176fin[[4*32-3]],diagslist176fin[[4*32-1]],diagslist176fin[[4*32]],
diagslist176fin[[4*20-3]],diagslist176fin[[4*20-1]],diagslist176fin[[4*20]],
diagslist176fin[[4*35-3]],diagslist176fin[[4*35-1]],diagslist176fin[[4*35]]}  /. q4-> pb-q1-q2-q3 //.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


exp4fire1group31= tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0) /. a_ Den[b___]-> Den[b]


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup31total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"total.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"total"]]


exp4firegroup31onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsection::Closed:: *)
(*group31u*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=311;
invsg311={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p1+p2)^2},{7,(k1+p2)^2},{8,(k1-p3)^2},{9,(k1+p1)^2},{10,(-p1-p2+pb)^2},{11,(+p2+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g311 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group311={diagslist176fin[[4*31-2]],
diagslist176fin[[4*19-2]],
diagslist176fin[[4*32-2]],
diagslist176fin[[4*20-2]],
diagslist176fin[[4*35-2]],
diagslist176fin[[4*38]]}  //.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1-q1,b___] :> (Den[a,k1-q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


exp4fire1group311= tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup311total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"total.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"total"]]


exp4firegroup311onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsection::Closed:: *)
(*group27 (massive props from here on) (+7)*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=27;
invsg27={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p1+p3)^2},{7,(k1-p2)^2},{8,(k1-pb)^2-mb2},{9,(k1-p1)^2},{10,(pb-p2-p3)^2},{11,(+p1+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props27=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g27 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,14,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (-F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0};


(* ::Text:: *)
(*Shift k-> k-q2 in one of the components (in denominator and numerator)*)


group27={diagslist176fin[[4*27-3]],diagslist176fin[[4*27-2]],diagslist176fin[[4*27-1]],
diagslist176fin[[4*15-3]],diagslist176fin[[4*15-2]],diagslist176fin[[4*15-1]],
diagslist176fin[[4*36-3]],diagslist176fin[[4*36-2]],diagslist176fin[[4*36-1]],
({diagslist176fin[[4*7-3]],diagslist176fin[[4*7-2]],diagslist176fin[[4*7-1]]}//. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. {Den[a___,k1-q4,b___] :> (Den[a,k1-q4,b] /. k1 :>   k1-q2 ),
s[a___,k1,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-24,b],s[a___,kk,b___] :> s[a,kk-k22,b]} //. {s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2],
s[a___,-12,c___]->-s[a,12,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-24,c___]->-s[a,24,c],s[a___,-k22,c___]->-2*s[a,k2,c]  } //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} ),
diagslist176fin[[4*3-3]],diagslist176fin[[4*3-2]],diagslist176fin[[4*3-1]]}   //. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //Flatten


group27part1={diagslist176fin[[4*27-3]],diagslist176fin[[4*27-2]],diagslist176fin[[4*27-1]],
diagslist176fin[[4*15-3]],diagslist176fin[[4*15-2]],diagslist176fin[[4*15-1]]}   //. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //Flatten


group27part2={({diagslist176fin[[4*7-3]],diagslist176fin[[4*7-2]],diagslist176fin[[4*7-1]]}//. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. {Den[a___,k1-q4,b___] :> (Den[a,k1-q4,b] /. k1 :>   k1-q2 ),
s[a___,k1,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-24,b],s[a___,kk,b___] :> s[a,kk-k22,b]} //. {s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2],
s[a___,-12,c___]->-s[a,12,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-24,c___]->-s[a,24,c],s[a___,-k22,c___]->-2*s[a,k2,c]  } //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} ),
diagslist176fin[[4*3-3]],diagslist176fin[[4*3-2]],diagslist176fin[[4*3-1]],
diagslist176fin[[4*36-3]],diagslist176fin[[4*36-2]],diagslist176fin[[4*36-1]]}   //. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //Flatten


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group27 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


exp4fire1group27part1 = tab[ToExpression["group"<>ToString[gnum]<>"part1"],ToExpression["repk1g"<>ToString[gnum]]]


exp4fire1group27part2 = tab[ToExpression["group"<>ToString[gnum]<>"part2"],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"part1.m",ToExpression["exp4fire1group"<>ToString[gnum]<>"part1"] /. F[a___]:> F[gnum,{a}]]
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"part2.m",ToExpression["exp4fire1group"<>ToString[gnum]<>"part2"] /. F[a___]:> F[gnum,{a}]]


exp4firegroup27total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


exp4firegroup27totalpart1=Total[ToExpression["exp4fire1group"<>ToString[gnum]<>"part2"] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};
exp4firegroup27totalpart2=Total[ToExpression["exp4fire1group"<>ToString[gnum]<>"part2"] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"totalpart1.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"totalpart1"] /. F[a___]:> F[gnum,{a}]]]
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"totalpart2.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"totalpart2"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup27onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


exp4firegroup27onlyintspart1 = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]<>"part1"]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}
exp4firegroup27onlyintspart2 = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]<>"part2"]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>"part1.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyintspart1"]]
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>"part2.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyintspart2"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators = props271;
MasterIntegrals[]
final271=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final271minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group27s*)


(* ::Subsubsection:: *)
(*Definitions*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=271;
invsg271={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p1+p3)^2},{7,(k1-p2)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p1-p2)^2},{11,(+p1+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props271=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


(* ::Subsubsection:: *)
(*Creation of the Integral-File and conversion to F[...]*)


repk1g271 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (-F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0};


(* ::Text:: *)
(*Shift k1-> k1+q2 in one of the parts , s[k22]=2s[k2]*)


group271={diagslist176fin[[4*27]],
diagslist176fin[[4*15]],
(diagslist176fin[[4*7]] //. {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 ),
Den[a___,k1+q4,b___] :> (Den[a,k1+q4,b] /. k1 :>   k1+q2),s[a___,k1,b___] :> s[a,k1+12,b],s[a___,k3,b___] :> s[a,k1+23,b],s[a___,k4,b___] :> s[a,k1+24,b],s[a___,kk,b___] :> s[a,kk+k22,b]} //.
{s[a___,k22,b___] :> 2*s[a,k2,b],s[k22] :> 2*s[k2]}),
diagslist176fin[[4*3]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //.
  s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2] /. s[a___,k22,b___]->2s[a,k2,b] 


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F],{i,1,Length[group]}];


exp4fire1group271 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup271total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup271onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =props271;
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},
				{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0}, {0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},
				{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},
				{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators = props271;
MasterIntegrals[]
final271=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final271minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group22 (+23)*)


(* ::Subsubsection:: *)
(*Definitions*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=22;
invsg22={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p2-p3)^2-mb2},{7,(k1-p2)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p1-p2)^2},{11,(+p1+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props22=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


(* ::Subsubsection:: *)
(*Creation of the Integral-File and conversion to F[...]*)


repk1g22 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,{k1-q1-q2-q3,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							(z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+
                                                                                                 z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group22={diagslist176fin[[4*22-3]],diagslist176fin[[4*22-1]],diagslist176fin[[4*22]],
diagslist176fin[[4*10-3]],diagslist176fin[[4*10-1]],diagslist176fin[[4*10]],
diagslist176fin[[4*43-3]],diagslist176fin[[4*43-1]],diagslist176fin[[4*43]],
diagslist176fin[[4*23-3]],diagslist176fin[[4*23-1]],diagslist176fin[[4*23]],
diagslist176fin[[4*11-3]],diagslist176fin[[4*11-1]],diagslist176fin[[4*11]],
diagslist176fin[[4*40-3]],diagslist176fin[[4*40-1]],diagslist176fin[[4*40]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )};


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group22 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup22total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup22onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators = ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final22=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final22minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group22u*)


(* ::Subsubsection:: *)
(*Definitions*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=221;
invsg221={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p2-p3)^2-mb2},{7,(k1-p2)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p1-p2)^2},{11,(+p2+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props221=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


(* ::Subsubsection:: *)
(*Creation of the Integral-File and conversion to F[...]*)


repk1g221 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,{k1-q1-q2-q3,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,34,b]-s[a,23,b]-s[a,14,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							(z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-13,a14]*s[a,b]+
                                                                                                 z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group221={diagslist176fin[[4*22-2]],
diagslist176fin[[4*10-2]],
diagslist176fin[[4*43-2]],
diagslist176fin[[4*23-2]],
diagslist176fin[[4*11-2]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )}


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group221 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup221total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup221onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final221=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final221minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group30 (+8)*)


(* ::Subsubsection:: *)
(*Definitions*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=30;
invsg30={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p1+p2)^2},{7,(k1-p2)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p2-p3)^2},{11,(+p1+p2-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props30=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


(* ::Subsubsection:: *)
(*Creation of the Integral-File and conversion to F[...]*)


repk1g30 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group30={diagslist176fin[[4*30-3]],diagslist176fin[[4*30-2]],diagslist176fin[[4*30]],
diagslist176fin[[4*18-3]],diagslist176fin[[4*18-2]],diagslist176fin[[4*18]],
diagslist176fin[[4*37-3]],diagslist176fin[[4*37-2]],diagslist176fin[[4*37]],
({diagslist176fin[[4*8-3]],diagslist176fin[[4*8-2]],diagslist176fin[[4*8]]} /. q4-> pb-q1-q2-q3 /. {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]} //. 
{Den[a___,k1-pb+q1+q2+q3,b___] :> (Den[a,k1-pb+q1+q2+q3,b] /. k1 :> k1-q3 ),
s[a___,k1,b___] :> s[a,k1-13,b],s[a___,k2,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-34,b],s[a___,kk,b___] :> s[a,kk-k32,b]}  )//. {s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2],
s[a___,-13,c___]->-s[a,13,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-34,c___]->-s[a,34,c],s[a___,-k32,c___]->-2*s[a,k3,c]  },
diagslist176fin[[4*4-3]],diagslist176fin[[4*4-2]],diagslist176fin[[4*4]],
diagslist176fin[[4*36]],diagslist176fin[[4*43-2]]} /. q4-> pb-q1-q2-q3  /. {Den[a___,k1+pb-q1-q2,b___] :> (Den[a,k1+pb-q1-q2,b] /. k1 :> -k1)}// Flatten


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group30 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup30total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup30onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


(* Last 4 tell FIRE that the respective propagators can only appear in the numerator *)
Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
Replacements={pb^2->mb2};
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},
{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},
{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
(*RESTRICTIONS = {{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};*)
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final30=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final30minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group30ubar*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=301;
invsg301={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p1+p2)^2},{7,(k1-p1)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p1-p3)^2},{11,(+p1+p2-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props301=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g301 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group301={diagslist176fin[[4*30-1]],
diagslist176fin[[4*18-1]],
(diagslist176fin[[4*8-1]] /. Den[a___] :> (Den[a] /. k1-> k1-q3)  //. { s[a___,k1,b___] :> s[a,k1-13,b],s[a___,k2,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-34,b],s[a___,kk,b___] :> s[a,kk-k32,b]} //. 
{s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2], s[a___,-13,c___]->-s[a,13,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-34,c___]->-s[a,34,c],s[a___,-k32,c___]->-2*s[a,k3,c]  }),
diagslist176fin[[4*4-1]],
diagslist176fin[[4*39]]} //. q4->pb-q1-q2-q3  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+pb-q1-q2,b___] :> (Den[a,k1+pb-q1-q2,b] /. k1 :>   -k1 ), Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 )}


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group301 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup301total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup301onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final301=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final301minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group24 (+6)*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=24;
invsg24={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p2+p3)^2},{7,(k1-p1)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p2-p3)^2},{11,(+p1+p3-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props24=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g24 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q2+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,14,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group24={diagslist176fin[[4*24-3]],diagslist176fin[[4*24-2]],diagslist176fin[[4*24-1]],
diagslist176fin[[4*12-3]],diagslist176fin[[4*12-2]],diagslist176fin[[4*12-1]],
diagslist176fin[[4*39-3]],diagslist176fin[[4*39-2]],diagslist176fin[[4*39-1]],
({diagslist176fin[[4*6-3]],diagslist176fin[[4*6-2]],diagslist176fin[[4*6-1]] } /. Den[a___] :> (Den[a] /. k1-> k1-q1)  //. { s[a___,k2,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-13,b],s[a___,k4,b___] :> s[a,k1-14,b],
s[a___,kk,b___] :> s[a,kk-k12,b]} //. 
{s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2], s[a___,-12,c___]->-s[a,12,c] ,s[a___,-13,c___]->-s[a,13,c],s[a___,-14,c___]->-s[a,14,c],s[a___,-k12,c___]->-2*s[a,k1,c]  }),
diagslist176fin[[4*2-3]],diagslist176fin[[4*2-2]],diagslist176fin[[4*2-1]],
diagslist176fin[[4*40-2]],diagslist176fin[[4*37-1]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), Den[a___,k1+q1+q4,b___] :> (Den[a,k1+q1+q4,b] /. k1 :>   -k1 )}  // Flatten


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group24 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup24total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup24onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final24=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final24minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group24s*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=241;
invsg241={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-pb+p2+p3)^2},{7,(k1-p1)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p2-p3)^2},{11,(+p1+p2-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props241=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g241 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,k1-pb+q2+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,34,b]-s[a,23,b]-s[a,14,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (-F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group241={diagslist176fin[[4*24]],
diagslist176fin[[4*12]],
({diagslist176fin[[4*6]] } /. Den[a___] :> (Den[a] /. k1-> k1-q1)  //. { s[a___,k2,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-13,b],s[a___,k4,b___] :> s[a,k1-14,b],
s[a___,kk,b___] :> s[a,kk-k12,b]} //. 
{s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2], s[a___,-12,c___]->-s[a,12,c] ,s[a___,-13,c___]->-s[a,13,c],s[a___,-14,c___]->-s[a,14,c],s[a___,-k12,c___]->-2*s[a,k1,c]  }),
diagslist176fin[[4*2]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), Den[a___,k1+q1+q4,b___] :> (Den[a,k1+q1+q4,b] /. k1 :>   -k1 )}   // Flatten


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group241 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup241total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup241onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final241=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final241minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group21 (+5)*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=21;
invsg21={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p2-p3)^2-mb2},{7,(k1-p1)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p2-p3)^2},{11,(+p1+p2-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props21=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g21 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,{k1-q1-q2-q3,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							(z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]) ,
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                (z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group21={diagslist176fin[[4*21-3]],diagslist176fin[[4*21-2]],diagslist176fin[[4*21]],
diagslist176fin[[4*9-3]],diagslist176fin[[4*9-2]],diagslist176fin[[4*9]],
diagslist176fin[[4*42-3]],diagslist176fin[[4*42-2]],diagslist176fin[[4*42]],
diagslist176fin[[4*5-3]],diagslist176fin[[4*5-2]],diagslist176fin[[4*5]],
diagslist176fin[[4*1-3]],diagslist176fin[[4*1-2]],diagslist176fin[[4*1]]} /. q4->pb-q1-q2-q3 /. Den[a___,{k1+pb,mb},c___,{k1+q1+q2+q3,mb},b___] :> (Den[a,{k1+pb,mb},c,{k1+q1+q2+q3,mb},b] /. k1->-k1)//. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,{-k1+c_,mb},b___] :> Den[a,{k1-c,mb},b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 )} 


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group21 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup21total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup21onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final21=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final21minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group21ubar*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=211;
invsg211={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p2-p3)^2-mb2},{7,(k1-p1)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p1-p3)^2},{11,(+p1+p2-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props211=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g211 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,{k1-q1-q2-q3,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							(z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]) ,
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                (z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group211={diagslist176fin[[4*21-1]],
diagslist176fin[[4*9-1]],
diagslist176fin[[4*42-1]],
diagslist176fin[[4*5-1]],
diagslist176fin[[4*1-1]]} /. q4->pb-q1-q2-q3 /. Den[a___,{k1+pb,mb},c___,{k1+q1+q2+q3,mb},b___] :> (Den[a,{k1+pb,mb},c,{k1+q1+q2+q3,mb},b] /. k1->-k1)//. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,{-k1+c_,mb},b___] :> Den[a,{k1-c,mb},b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 )} 


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group211 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup211total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup211onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final211=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final211minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group27 (+7) REMASTERED*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=27;
invsg27={{1,(p1)^2},{2,p2^2},{3,p3^2},{4,(pb-p1-p2-p3)^2},{5,(p1+p2+p3)^2-z},
{6,(k1)^2},{7,(k1-pb+p1+p3)^2},{8,(k1-p2)^2},{9,(k1-pb)^2-mb2},{10,(k1-p3)^2},
{11,(pb-p2-p3)^2},{12,(+p1+p3-pb)^2},{13,(p1+p2)^2},{14,(p2+p3)^2}};
props27=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g27 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12+1,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,14,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b]-
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (-F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a1<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0};


(* ::Text:: *)
(*Shift k-> k-q2 in one of the components (in denominator and numerator)*)


group27={diagslist176fin[[4*27-3]],diagslist176fin[[4*27-2]],diagslist176fin[[4*27-1]],
diagslist176fin[[4*15-3]],diagslist176fin[[4*15-2]],diagslist176fin[[4*15-1]],
diagslist176fin[[4*36-3]],diagslist176fin[[4*36-2]],diagslist176fin[[4*36-1]],
({diagslist176fin[[4*7-3]],diagslist176fin[[4*7-2]],diagslist176fin[[4*7-1]]}//. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. {Den[a___,k1-q4,b___] :> (Den[a,k1-q4,b] /. k1 :>   k1-q2 ),
s[a___,k1,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-24,b],s[a___,kk,b___] :> s[a,kk-k22,b]} //. {s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2],
s[a___,-12,c___]->-s[a,12,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-24,c___]->-s[a,24,c],s[a___,-k22,c___]->-2*s[a,k2,c]  } //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} ),
diagslist176fin[[4*3-3]],diagslist176fin[[4*3-2]],diagslist176fin[[4*3-1]]}   //. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //Flatten


g27exchange23=group27 /. q2-> p3 /. q3->p2 /. p3->q3 /. p2->q2 


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


g27exchange23F=tab[g27exchange23,ToExpression["repk1g"<>ToString[30]]] /. F[a___]:> F[30,{a}]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["~/BSGamma/lm/Mathematica/group"<>ToString[gnum]<>"REMASTERED.m",g27exchange23F]


exp4firegroup27total=Total[g27exchange23F] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["~/BSGamma/lm/Mathematica/group"<>ToString[gnum]<>"totalREMASTERED.m",exp4firegroup27total]


exp4firegroup27onlyints = Union[List@@Plus[ Expand[exp4firegroup27total //. a_ *F[b___]->F[b]]]]  


Export["~/BSGamma/lm/Mathematica/topclass"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/lars/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
Replacements={pb^2->mb2};
RESTRICTIONS ={{0, 0, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {0, 0, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {0, 0, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {0, 0, -1, 0, 0,0,0,0,0,0,0,0,0,0}, 
{0, 0, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {0, 0, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {0, 0, -1, -1, -1,0,0,0,0,0,0,0,0,0}, {0, -1, 0, 0, 0,0,0,0,0,0,0,0,0,0},
{0, -1, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {0, -1, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {0, -1, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {0, -1, -1, 0, 0,0,0,0,0,0,0,0,0,0},
{0, -1, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {0, -1, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {0, -1, -1, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0},
{-1, 0, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, 0, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, -1, 0, 0,0,0,0,0,0,0,0,0,0}, 
{-1, 0, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, 0, -1, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, 0, 0, 0,0,0,0,0,0,0,0,0,0},
{-1, -1, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, -1, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, -1, 0, 0,0,0,0,0,0,0,0,0,0}, 
{-1, -1, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, -1, -1, -1, -1,0,0,0,0,0,0,0,0,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/lars/Dokumente/BSGamma/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators = props271;
MasterIntegrals[]
final271=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final271minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection::Closed:: *)
(*group30 (+8) REMASTERED*)


(* ::Subsubsection:: *)
(*Creation of the .start file*)


(* Last 4 tell FIRE that the respective propagators can only appear in the numerator *)
Get["~/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
Replacements={pb^2->mb2};
RESTRICTIONS ={{0, 0, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {0, 0, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {0, 0, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {0, 0, -1, 0, 0,0,0,0,0,0,0,0,0,0}, 
{0, 0, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {0, 0, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {0, 0, -1, -1, -1,0,0,0,0,0,0,0,0,0}, {0, -1, 0, 0, 0,0,0,0,0,0,0,0,0,0},
{0, -1, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {0, -1, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {0, -1, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {0, -1, -1, 0, 0,0,0,0,0,0,0,0,0,0},
{0, -1, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {0, -1, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {0, -1, -1, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0},
{-1, 0, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, 0, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, -1, 0, 0,0,0,0,0,0,0,0,0,0}, 
{-1, 0, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, 0, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, 0, -1, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, 0, 0, 0,0,0,0,0,0,0,0,0,0},
{-1, -1, 0, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, 0, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, -1, 0, -1, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, -1, 0, 0,0,0,0,0,0,0,0,0,0}, 
{-1, -1, -1, 0, -1,0,0,0,0,0,0,0,0,0}, {-1, -1, -1, -1, 0,0,0,0,0,0,0,0,0,0}, {-1, -1, -1, -1, -1,0,0,0,0,0,0,0,0,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/lars/Dokumente/BSGamma/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final30=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final30minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Subsection:: *)
(*combining the integrals of family g28 (no massive propagator in loop) (still need to add and remaster)*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsO3O3uuBeforeIBP.m"];
gnum=28;
invsg28={{1,(p1)^2},{2,p2^2},{3,p3^2},{4,(pb-p1-p2-p3)^2},{5,(p1+p2+p3)^2-z},{6,(k1)^2},{7,(k1-p1-p3+pb)^2},{8,(k1+p2)^2},{9,(k1-p3)^2},{10,(k1-p1)^2},{11,(-p1-p3+pb)^2},{12,(+p2+p3-pb)^2},{13,(p1+p3)^2},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g28 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b], 
			(* replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b] ,
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12+1,a13,a14]*Den[a,b],
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,24,b] ,
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2(F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+ 
																							z* F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - 
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b] + 
																							F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - 
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			(* invariants containing the loop momenta: *)
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																			                      F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1, 
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a1<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


(* ::Subsubsection:: *)
(*g28*)


group28={diagslist176fin[[4*28-3]],diagslist176fin[[4*28-2]],diagslist176fin[[4*28-1]],
diagslist176fin[[4*16-3]],diagslist176fin[[4*16-2]],diagslist176fin[[4*16-1]],
diagslist176fin[[4*33-3]],diagslist176fin[[4*33-2]],diagslist176fin[[4*33-1]],
diagslist176fin[[4*29-3]],diagslist176fin[[4*29-2]],diagslist176fin[[4*29-1]],
diagslist176fin[[4*17-3]],diagslist176fin[[4*17-2]],diagslist176fin[[4*17-1]],
diagslist176fin[[4*38-3]],diagslist176fin[[4*38-2]],diagslist176fin[[4*38-1]]}/.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


exp4fire1group28= tab[group28,repk1g28] /. F[a___]:> F[28,{a}]


% - (% /. Den[___]->0) /. a_ Den[b___]-> Den[b]


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28.m",exp4fire1group28 ]


exp4firegroup28total=Total[exp4fire1group28 ] //.
 {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]:> 0;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28total.m",exp4firegroup28total]


exp4firegroup28onlyints = Union[List@@Plus[ Expand[exp4firegroup28total] //.
a_ *F[b___]->F[b]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass28.m",exp4firegroup28onlyints]


(* ::Subsection::Closed:: *)
(*combining the integrals of family g30*)


(* ::Subsubsection:: *)
(*Definitions*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=30;
invsg30={{1,(p1)^2},{2,p2^2},{3,p3^2},{4,(pb-p1-p2-p3)^2},{5,(p1+p2+p3)^2-z},{6,(k1)^2},{7,(k1-pb+p1+p2)^2},{8,(k1-p2)^2},
{9,(k1-pb)^2-mb2},{10,(k1-p3)^2},{11,(pb-p2-p3)^2},{12,(+p1+p2-pb)^2},{13,(p1+p3)^2},{14,(p2+p3)^2}};
props30=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


(* ::Subsubsection::Closed:: *)
(*g30*)


repk1g30 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), 
			Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b] ,
			Den[a___,k1-pb+q1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->
			F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->
			F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->
			F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->
			F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->
			F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->
			F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12+1,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(-F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,-1a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a1<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group30={diagslist176fin[[4*30-3]],diagslist176fin[[4*30-2]],diagslist176fin[[4*30]],
diagslist176fin[[4*18-3]],diagslist176fin[[4*18-2]],diagslist176fin[[4*18]],
diagslist176fin[[4*37-3]],diagslist176fin[[4*37-2]],diagslist176fin[[4*37]],
({diagslist176fin[[4*8-3]],diagslist176fin[[4*8-2]],diagslist176fin[[4*8]]} /. q4-> pb-q1-q2-q3 /. {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]} //. 
{Den[a___,k1-pb+q1+q2+q3,b___] :> (Den[a,k1-pb+q1+q2+q3,b] /. k1 :> k1-q3 ),
s[a___,k1,b___] :> s[a,k1-13,b],s[a___,k2,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-34,b],s[a___,kk,b___] :> s[a,kk-k32,b]}  )//. {s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2],
s[a___,-13,c___]->-s[a,13,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-34,c___]->-s[a,34,c],s[a___,-k32,c___]->-2*s[a,k3,c]  },
diagslist176fin[[4*4-3]],diagslist176fin[[4*4-2]],diagslist176fin[[4*4]],
diagslist176fin[[4*36]],diagslist176fin[[4*43-2]]} /. q4-> pb-q1-q2-q3  /. {Den[a___,k1+pb-q1-q2,b___] :> (Den[a,k1+pb-q1-q2,b] /. k1 :> -k1)}// Flatten


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group30 = tab[ToExpression["group"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup30total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"totalREMASTERED.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firegroup30onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup30total  /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//.
a_ *F[b___]->F[b]]]] 


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[30]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection::Closed:: *)
(*g27*)


gnum=27;
group27={diagslist176fin[[4*27-3]],diagslist176fin[[4*27-2]],diagslist176fin[[4*27-1]],
diagslist176fin[[4*15-3]],diagslist176fin[[4*15-2]],diagslist176fin[[4*15-1]],
diagslist176fin[[4*36-3]],diagslist176fin[[4*36-2]],diagslist176fin[[4*36-1]],
({diagslist176fin[[4*7-3]],diagslist176fin[[4*7-2]],diagslist176fin[[4*7-1]]}//. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. {Den[a___,k1-q4,b___] :> (Den[a,k1-q4,b] /. k1 :>   k1-q2 ),
s[a___,k1,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-24,b],s[a___,kk,b___] :> s[a,kk-k22,b]} //. {s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2],
s[a___,-12,c___]->-s[a,12,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-24,c___]->-s[a,24,c],s[a___,-k22,c___]->-2*s[a,k2,c]  } //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} ),
diagslist176fin[[4*3-3]],diagslist176fin[[4*3-2]],diagslist176fin[[4*3-1]]}   //. { Den[a___,-k1+c_,b___] :> Den[a,k1-c,b]}  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //Flatten


g27exchange23=group27 /. q2-> p3 /. q3->p2 /. p3->q3 /. p2->q2 //.  {s[a___,12,b___]->s[a,p13,b],s[a___,13,b___]->s[a,p12,b],s[a___,23,b___]->s[a,p23,b],
s[a___,24,b___]->s[a,p34,b],s[a___,34,b___]->s[a,p24,b],s[a___,14,b___]->s[a,p14,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


g27exchange23F=tab[g27exchange23,ToExpression["repk1g"<>ToString[30]]] /. F[a___]:> F[30,{a}]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"REMASTERED.m",g27exchange23F]


exp4firegroup27total=Total[g27exchange23F] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"totalREMASTERED.m",exp4firegroup27total]


exp4firegroup27onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup27total  /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection::Closed:: *)
(*g271*)


gnum=271;
diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
group271={diagslist176fin[[4*27]],
diagslist176fin[[4*15]],
(diagslist176fin[[4*7]] //. {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 ),
Den[a___,k1+q4,b___] :> (Den[a,k1+q4,b] /. k1 :>   k1+q2),s[a___,k1,b___] :> s[a,k1+12,b],s[a___,k3,b___] :> s[a,k1+23,b],s[a___,k4,b___] :> s[a,k1+24,b],s[a___,kk,b___] :> s[a,kk+k22,b]} //.
{s[a___,k22,b___] :> 2*s[a,k2,b],s[k22] :> 2*s[k2]}),
diagslist176fin[[4*3]],diagslist176fin[[4*42-1]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )} //.
  s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2] /. s[a___,k22,b___]->2s[a,k2,b] 


g271exchange123cyc=group271 /. q4 -> pb-q1-q2-q3  //. {q2-> p3, q3->p1, q1->p2} //. {p1->q1, p2->q2, p3->q3 }  //.  {s[a___,12,b___]->s[a,p23,b],s[a___,13,b___]->s[a,p12,b],s[a___,23,b___]->s[a,p13,b],
s[a___,24,b___]->s[a,p34,b],s[a___,34,b___]->s[a,p14,b],s[a___,14,b___]->s[a,p24,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


g271exchange123cycF=tab[g271exchange123cyc,ToExpression["repk1g"<>ToString[30]]] /. F[a___]:> F[30,{a}]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"REMASTERED.m",g271exchange123cycF]


exp4firegroup271total=Total[g271exchange123cycF] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"totalREMASTERED.m",exp4firegroup271total]


exp4firegroup271onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup271total  /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection::Closed:: *)
(*g24*)


gnum=24;
group24={diagslist176fin[[4*24-3]],diagslist176fin[[4*24-2]],diagslist176fin[[4*24-1]],
diagslist176fin[[4*12-3]],diagslist176fin[[4*12-2]],diagslist176fin[[4*12-1]],
diagslist176fin[[4*39-3]],diagslist176fin[[4*39-2]],diagslist176fin[[4*39-1]],
({diagslist176fin[[4*6-3]],diagslist176fin[[4*6-2]],diagslist176fin[[4*6-1]] } /. Den[a___] :> (Den[a] /. k1-> k1-q1)  //. { s[a___,k2,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-13,b],s[a___,k4,b___] :> s[a,k1-14,b],
s[a___,kk,b___] :> s[a,kk-k12,b]} //. 
{s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2], s[a___,-12,c___]->-s[a,12,c] ,s[a___,-13,c___]->-s[a,13,c],s[a___,-14,c___]->-s[a,14,c],s[a___,-k12,c___]->-2*s[a,k1,c]  }),
diagslist176fin[[4*2-3]],diagslist176fin[[4*2-2]],diagslist176fin[[4*2-1]],
diagslist176fin[[4*40-2]],diagslist176fin[[4*37-1]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), Den[a___,k1+q1+q4,b___] :> (Den[a,k1+q1+q4,b] /. k1 :>   -k1 )}  // Flatten


g24exchange123anticyc=group24 /. q4 -> pb-q1-q2-q3  //. {q2-> p1, q3->p2, q1->p3} //. {p1->q1, p2->q2, p3->q3 } //.  {s[a___,12,b___]->s[a,p13,b],s[a___,13,b___]->s[a,p23,b],s[a___,23,b___]->s[a,p12,b],
s[a___,24,b___]->s[a,p14,b],s[a___,34,b___]->s[a,p24,b],s[a___,14,b___]->s[a,p34,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


g24exchange123anticycF=tab[g24exchange123anticyc,ToExpression["repk1g"<>ToString[30]]] /. F[a___]:> F[30,{a}]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"REMASTERED.m",g24exchange123anticycF]


exp4firegroup24total=Total[g24exchange123anticycF] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"totalREMASTERED.m",exp4firegroup24total]


exp4firegroup24onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup24total  /. Dcoeff[0,0,0,0]->0 /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection::Closed:: *)
(*g241*)


gnum=241;
group241={diagslist176fin[[4*24]],
diagslist176fin[[4*12]],
({diagslist176fin[[4*6]] } /. Den[a___] :> (Den[a] /. k1-> k1-q1)  //. { s[a___,k2,b___] :> s[a,k1-12,b],s[a___,k3,b___] :> s[a,k1-13,b],s[a___,k4,b___] :> s[a,k1-14,b],
s[a___,kk,b___] :> s[a,kk-k12,b]} //. 
{s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2], s[a___,-12,c___]->-s[a,12,c] ,s[a___,-13,c___]->-s[a,13,c],s[a___,-14,c___]->-s[a,14,c],s[a___,-k12,c___]->-2*s[a,k1,c]  }),
diagslist176fin[[4*2]],diagslist176fin[[4*42-2]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), Den[a___,k1+q1+q4,b___] :> (Den[a,k1+q1+q4,b] /. k1 :>   -k1 )}   // Flatten


g241exchange13=group241 /. q4 -> pb-q1-q2-q3  //. {q3->p1, q1->p3} //. {p1->q1, p2->q2, p3->q3 } //.  {s[a___,12,b___]->s[a,p23,b],s[a___,13,b___]->s[a,p13,b],s[a___,23,b___]->s[a,p12,b],
s[a___,24,b___]->s[a,p24,b],s[a___,34,b___]->s[a,p14,b],s[a___,14,b___]->s[a,p34,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


g241exchange13F=tab[g241exchange13,ToExpression["repk1g"<>ToString[30]]] /. F[a___]:> F[30,{a}]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"REMASTERED.m",g241exchange13F]


exp4firegroup241total=Total[g241exchange13F] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"totalREMASTERED.m",exp4firegroup241total]


exp4firegroup241onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup241total /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection::Closed:: *)
(*g301*)


gnum=301;
group301={diagslist176fin[[4*30-1]],
diagslist176fin[[4*18-1]],
(diagslist176fin[[4*8-1]] /. Den[a___] :> (Den[a] /. k1-> k1-q3)  //. { s[a___,k1,b___] :> s[a,k1-13,b],s[a___,k2,b___] :> s[a,k1-23,b],s[a___,k4,b___] :> s[a,k1-34,b],s[a___,kk,b___] :> s[a,kk-k32,b]} //. 
{s[a1___,Plus[a_,b_],a2___]-> s[a1,a,a2]+s[a1,b,a2], s[a___,-13,c___]->-s[a,13,c] ,s[a___,-23,c___]->-s[a,23,c],s[a___,-34,c___]->-s[a,34,c],s[a___,-k32,c___]->-2*s[a,k3,c]  }),
diagslist176fin[[4*4-1]],
diagslist176fin[[4*39]]} //. q4->pb-q1-q2-q3  //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+pb-q1-q2,b___] :> (Den[a,k1+pb-q1-q2,b] /. k1 :>   -k1 ), Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 )}


g301exchange12=group301 /. q4 -> pb-q1-q2-q3  //. {q2->p1, q1->p2} //. {p1->q1, p2->q2, p3->q3 } //.  {s[a___,12,b___]->s[a,p12,b],s[a___,13,b___]->s[a,p23,b],s[a___,23,b___]->s[a,p13,b],
s[a___,24,b___]->s[a,p14,b],s[a___,34,b___]->s[a,p34,b],s[a___,14,b___]->s[a,p24,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


g301exchange12F=tab[g301exchange12,ToExpression["repk1g"<>ToString[30]]] /. F[a___]:> F[30,{a}]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"REMASTERED.m",g301exchange12F]


exp4firegroup301total=Total[g301exchange12F] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[gnum]<>"totalREMASTERED.m",exp4firegroup301total]


exp4firegroup301onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup301total /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[gnum]<>"REMASTERED.m",ToExpression["exp4firegroup"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Unification of the Integrals*)


t30=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass30REMASTERED.m"];
t301=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass301REMASTERED.m"];
t24=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass24REMASTERED.m"];
t241=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass241REMASTERED.m"];
t27=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass27REMASTERED.m"];
t271=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass271REMASTERED.m"];


Join[group30,group301,group27,group271,group24,group241] // Length


allintsFam1mass=Join[t30,t301,t24,t241,t27,t271] // Union


Export["/home/users/moos/BSGamma/lm/Mathematica/allintsFAM1Mass.m",allintsFam1mass]


(* ::Subsection::Closed:: *)
(*combining the integrals of family g22*)


(* ::Subsubsection:: *)
(*definition of the groups and rules*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
group21={diagslist176fin[[4*21-3]],
diagslist176fin[[4*9-3]],
diagslist176fin[[4*21-1]],
diagslist176fin[[4*9-1]],
diagslist176fin[[4*42-3]],
diagslist176fin[[4*21]],
diagslist176fin[[4*9]],
diagslist176fin[[4*42]],
diagslist176fin[[4*5-1]],
diagslist176fin[[4*5-3]],
diagslist176fin[[4*5]],
diagslist176fin[[4*1-1]],
diagslist176fin[[4*1-3]],
diagslist176fin[[4*1]],
diagslist176fin[[4*5-2]],
diagslist176fin[[4*1-2]]} /. q4->pb-q1-q2-q3 /. Den[a___,{k1+pb,mb},c___,{k1+q1+q2+q3,mb},b___] :> (Den[a,{k1+pb,mb},c,{k1+q1+q2+q3,mb},b] /. k1->-k1)//. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,{-k1+c_,mb},b___] :> Den[a,{k1-c,mb},b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 )};
 group211={diagslist176fin[[4*21-2]],
diagslist176fin[[4*9-2]]} /. q4->pb-q1-q2-q3 /. Den[a___,{k1+pb,mb},c___,{k1+q1+q2+q3,mb},b___] :> (Den[a,{k1+pb,mb},c,{k1+q1+q2+q3,mb},b] /. k1->-k1)//. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,{-k1+c_,mb},b___] :> Den[a,{k1-c,mb},b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 )} ; 
group22={diagslist176fin[[4*22-3]],
diagslist176fin[[4*10-3]],
diagslist176fin[[4*23-3]],
diagslist176fin[[4*11-3]],
diagslist176fin[[4*22-1]],
diagslist176fin[[4*10-1]],
diagslist176fin[[4*43-1]],
diagslist176fin[[4*22]],
diagslist176fin[[4*10]],
diagslist176fin[[4*43]],
diagslist176fin[[4*43-3]],
diagslist176fin[[4*11-1]],
diagslist176fin[[4*23-1]],
diagslist176fin[[4*40]],
diagslist176fin[[4*40-1]],
diagslist176fin[[4*40-3]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )};
 group221={
 diagslist176fin[[4*22-2]],
diagslist176fin[[4*10-2]],
diagslist176fin[[4*23-2]],
diagslist176fin[[4*11-2]],
diagslist176fin[[4*23]],
diagslist176fin[[4*11]]} //. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,k1+q2,b___] :> (Den[a,k1+q2,b] /. k1 :>   -k1 ), Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ), 
 Den[a___,k1+q2+q4,b___] :> (Den[a,k1+q2+q4,b] /. k1 :>   -k1 )};
 Join[group21,group211,group22,group221] // Length


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsBeforeIBP.m"];
gnum=22;
invsg22={{1,(p1)^2},{2,p2^2},{3,p3^2},{4,(pb-p1-p2-p3)^2},{5,(p1+p2+p3)^2-z},{6,(k1)^2},{7,(k1-p1-p2-p3)^2-mb2},{8,(k1-p2)^2},{9,(k1-pb)^2-mb2},{10,(k1-p3)^2},{11,(pb-p1-p2)^2},{12,(+p1+p3-pb)^2},{13,(p1+p3)^2},{14,(p2+p3)^2}};
props22=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g22 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b] ,
			Den[a___,{k1-q1-q2-q3,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12+1,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,14,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,24,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
																							(z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a1<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


(* ::Subsubsection:: *)
(*no change*)


fam22nochange=Join[group22,group221[[5;;6]],group21[[9;;14]]] 


exp4fire1group22nochange = tab[fam22nochange,ToExpression["repk1g"<>ToString[22]]] /. F[a___]:> F[22,{a}]


exp4fire1group22nochange - (exp4fire1group22nochange /. Den[___]->0)
exp4fire1group22nochange - (exp4fire1group22nochange /. s[___]->0)


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[22]<>"nochangeREMASTERED.m",exp4fire1group22nochange]


exp4firegroup22nochangetotal=Total[exp4fire1group22nochange] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[22]<>"nochangetotalREMASTERED.m",exp4firegroup22nochangetotal]


exp4firegroup22nochangeonlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup22nochangetotal /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[22]<>"nochangeREMASTERED.m",ToExpression["exp4firegroup"<>ToString[22]<>"nochangeonlyints"]]


(* ::Subsubsection::Closed:: *)
(*change 13*)


fam22change13=Join[group221[[1;;2]],group21[[1;;4]],{group211[[1]]}] /. q4 -> pb-q1-q2-q3  //. {q3->p1, q1->p3} //. {p1->q1, p2->q2, p3->q3 } //.  {s[a___,12,b___]->s[a,p23,b],s[a___,13,b___]->s[a,p13,b],s[a___,23,b___]->s[a,p12,b],
s[a___,24,b___]->s[a,p24,b],s[a___,34,b___]->s[a,p14,b],s[a___,14,b___]->s[a,p34,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


exp4fire1group22change13=tab[fam22change13,ToExpression["repk1g"<>ToString[22]]] /. F[a___]:> F[22,{a}]


exp4fire1group22change13 - (exp4fire1group22change13 /. Den[___]->0)
exp4fire1group22change13 - (exp4fire1group22change13 /. s[___]->0)


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[22]<>"change13REMASTERED.m",exp4fire1group22change13]


exp4firegroup22change13total=Total[exp4fire1group22change13] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[22]<>"change13totalREMASTERED.m",exp4firegroup22change13total]


exp4firegroup22change13onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup22change13total /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[22]<>"change13REMASTERED.m",ToExpression["exp4firegroup"<>ToString[22]<>"change13onlyints"]]


(* ::Subsubsection::Closed:: *)
(*change 12*)


fam22change12=Join[group221[[3;;4]],group21[[5;;8]],group21[[15;;16]]]  /. q4 -> pb-q1-q2-q3  //. {q2->p1, q1->p2} //. {p1->q1, p2->q2, p3->q3 } //.  {s[a___,12,b___]->s[a,p12,b],s[a___,13,b___]->s[a,p23,b],s[a___,23,b___]->s[a,p13,b],
s[a___,24,b___]->s[a,p14,b],s[a___,34,b___]->s[a,p34,b],s[a___,14,b___]->s[a,p24,b]} //.  {s[a___,p12,b___]->s[a,12,b],s[a___,p13,b___]->s[a,13,b],s[a___,p23,b___]->s[a,23,b],
s[a___,p24,b___]->s[a,24,b],s[a___,p34,b___]->s[a,34,b],s[a___,p14,b___]->s[a,14,b]}


exp4fire1group22change12 = tab[fam22change12,ToExpression["repk1g"<>ToString[22]]] /. F[a___]:> F[22,{a}]


exp4fire1group22change12 - (exp4fire1group22change12 /. Den[___]->0)
exp4fire1group22change12 - (exp4fire1group22change12 /. s[___]->0)


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[22]<>"change12REMASTERED.m",exp4fire1group22change12]


exp4firegroup22change12total=Total[exp4fire1group22change12] //. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0 ;


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group"<>ToString[22]<>"change12totalREMASTERED.m",exp4firegroup22change12total]


exp4firegroup22change12onlyints = Union[List@@Plus[ Expand[Collect[exp4firegroup22change12total /. Dcoeff[a1_,a2_,a3_,a4_]-> a1+ a2 d+ a3 d^2 +a4 d^3 ,_F,Factor]//. a_ *F[b___]->F[b]]]]  


Export["~/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass"<>ToString[22]<>"change12REMASTERED.m",ToExpression["exp4firegroup"<>ToString[22]<>"change12onlyints"]]


(* ::Subsubsection::Closed:: *)
(*Collection of the integrals*)


t22nochange=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass22nochangeREMASTERED.m"];
t22change13=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass22change13REMASTERED.m"];
t22change12=Import["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass22change12REMASTERED.m"];

allintsFam2mass=Join[t22nochange,t22change13,t22change12] // Union
Export["/home/users/moos/BSGamma/lm/Mathematica/allintsFAM2Mass.m",allintsFam2mass]


(* ::Subsubsection:: *)
(*create .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/BSGamma/lm/Mathematica/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*shifted to others*)


fam2shifttoothers=Join[group221[[7;;8]],group211[[2;;3]]] 


(* ::Subsection:: *)
(*General Form of the Procedure*)


group28[diagslist176fin_]:={diagslist176fin[[diagnumsg28]]}/.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


diagnumsg28 = {109,110,111,61,62,63,129,130,131,113,114,115,65,66,67,149,150,151};


group28[Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsO3O5uuBeforeIBP.m"]] // Flatten


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


DiagsToIntegrals[groupnum_,operators_,probnum_] := Module[{diaglist,protolist,protolisttotal,group,onlyints,path},
path="/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/G";
diaglist=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176Diagrams"<>ToString[operators]<>"BeforeIBP.m"] ;
group= Flatten[ToExpression["group"<>ToString[groupnum]][diaglist]];
protolist = tab[group,ToExpression["repk1g"<>ToString[probnum]]]  /. F[a___]:> F[probnum,{a}];
protolisttotal=Total[protolist]//.
 {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]:> 0;
onlyints = Union[List@@Plus[Expand[protolisttotal] //. a_ *F[b___]->F[b]]];
Export[path<>ToString[probnum]<>"/group"<>ToString[groupnum]<>ToString[operators]<>".m",protolist];
Export[path<>ToString[probnum]<>"/group"<>ToString[groupnum]<>ToString[operators]<>"total.m",protolisttotal];
Export[path<>ToString[probnum]<>"/topclass"<>ToString[groupnum]<>ToString[operators]<>".m",onlyints];
];


DiagsToIntegrals[28,O3O3uu,28];
DiagsToIntegrals[28,O3O5uu,28];
DiagsToIntegrals[28,O5O3uu,28];
DiagsToIntegrals[28,O5O5uu,28];


(* ::Subsection:: *)
(*group28_O3O5uu*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsO3O5uuBeforeIBP.m"];
gnum=28;
invsg28={{1,(p1)^2},{2,p2^2},{3,p3^2},{4,(pb-p1-p2-p3)^2},{5,(p1+p2+p3)^2-z},{6,(k1)^2},{7,(k1-p1-p3+pb)^2},{8,(k1+p2)^2},{9,(k1-p3)^2},{10,(k1-p1)^2},{11,(-p1-p3+pb)^2},{12,(+p2+p3-pb)^2},{13,(p1+p3)^2},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g28 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b], 
			(* replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b] ,
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12+1,a13,a14]*Den[a,b],
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,24,b] ,
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2(F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+ 
																							z* F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - 
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b] + 
																							F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - 
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			(* invariants containing the loop momenta: *)
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																			                      F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1, 
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a1<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group28={diagslist176fin[[4*28-3]],diagslist176fin[[4*28-2]],diagslist176fin[[4*28-1]],
diagslist176fin[[4*16-3]],diagslist176fin[[4*16-2]],diagslist176fin[[4*16-1]],
diagslist176fin[[4*33-3]],diagslist176fin[[4*33-2]],diagslist176fin[[4*33-1]],
diagslist176fin[[4*29-3]],diagslist176fin[[4*29-2]],diagslist176fin[[4*29-1]],
diagslist176fin[[4*17-3]],diagslist176fin[[4*17-2]],diagslist176fin[[4*17-1]],
diagslist176fin[[4*38-3]],diagslist176fin[[4*38-2]],diagslist176fin[[4*38-1]]}/.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


exp4fire1group28= tab[group28,repk1g28]  /. F[a___]:> F[28,{a}]


% - (% /. Den[___]->0) /. a_ Den[b___]-> Den[b]


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28.m",exp4fire1group28]


exp4firegroup28total=Total[exp4fire1group28 ]//. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28total.m",exp4firegroup28total]


exp4firegroup28onlyintsO3O5 = Union[List@@Plus[ Expand[Total[exp4fire1group28]] //.
a_ *F[b___]->F[b]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass28.m",exp4firegroup28onlyints]


(* ::Subsection:: *)
(*group28_O5O3uu*)


diagslist176fin=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsO5O3uuBeforeIBP.m"];
gnum=28;
invsg28={{1,(p1)^2},{2,p2^2},{3,p3^2},{4,(pb-p1-p2-p3)^2},{5,(p1+p2+p3)^2-z},{6,(k1)^2},{7,(k1-p1-p3+pb)^2},{8,(k1+p2)^2},{9,(k1-p3)^2},{10,(k1-p1)^2},{11,(-p1-p3+pb)^2},{12,(+p2+p3-pb)^2},{13,(p1+p3)^2},{14,(p2+p3)^2}};
Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g28 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b], 
			(* replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,1,0,0,0,0,0,0,0,0]*Den[a,b] ,
			Den[a___,k1+q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1+pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12+1,a13,a14]*Den[a,b],
			s[a___,34,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,24,b] ,
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2(F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5-1,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+ 
																							z* F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - 
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b] + 
																							F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] +
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b] - 
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,24,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			(* invariants containing the loop momenta: *)
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																			                      F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
							                                                                        F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1, 
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a1<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


group28={diagslist176fin[[4*28-3]],diagslist176fin[[4*28-2]],diagslist176fin[[4*28-1]],
diagslist176fin[[4*16-3]],diagslist176fin[[4*16-2]],diagslist176fin[[4*16-1]],
diagslist176fin[[4*33-3]],diagslist176fin[[4*33-2]],diagslist176fin[[4*33-1]],
diagslist176fin[[4*29-3]],diagslist176fin[[4*29-2]],diagslist176fin[[4*29-1]],
diagslist176fin[[4*17-3]],diagslist176fin[[4*17-2]],diagslist176fin[[4*17-1]],
diagslist176fin[[4*38-3]],diagslist176fin[[4*38-2]],diagslist176fin[[4*38-1]]}/.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule,
_F,Simplify],{i,1,Length[group]}];


exp4fire1group28= tab[group28,repk1g28]  /. F[a___]:> F[28,{a}]


% - (% /. Den[___]->0) /. a_ Den[b___]-> Den[b]


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28.m",exp4fire1group28]


exp4firegroup28total=Total[exp4fire1group28 ]//. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28total.m",exp4firegroup28total]


exp4firegroup28onlyintsO5O3 = Union[List@@Plus[ Expand[Total[exp4fire1group28]] //.
a_ *F[b___]->F[b]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass28.m",exp4firegroup28onlyints]


(* ::Subsection:: *)
(*group28_O5O5uu*)


diagslist176finO5O5=Import["/home/users/moos/BSGamma/lm/Mathematica/diagsfromFORM/All176DiagramsO5O5uuBeforeIBP.m"];
group28O5O5={diagslist176finO5O5[[4*28-3]],diagslist176finO5O5[[4*28-2]],diagslist176finO5O5[[4*28-1]],
diagslist176finO5O5[[4*16-3]],diagslist176finO5O5[[4*16-2]],diagslist176finO5O5[[4*16-1]],
diagslist176finO5O5[[4*33-3]],diagslist176finO5O5[[4*33-2]],diagslist176finO5O5[[4*33-1]],
diagslist176finO5O5[[4*29-3]],diagslist176finO5O5[[4*29-2]],diagslist176finO5O5[[4*29-1]],
diagslist176finO5O5[[4*17-3]],diagslist176finO5O5[[4*17-2]],diagslist176finO5O5[[4*17-1]],
diagslist176finO5O5[[4*38-3]],diagslist176finO5O5[[4*38-2]],diagslist176finO5O5[[4*38-1]]}/.
{ Den[a___,-k1+c_,b___] :> Den[a,k1-c,b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 ),Den[a___,k1+q3,b___] :> (Den[a,k1+q3,b] /. k1 :>   -k1 ) }


exp4fire1group28O5O5= tab[group28O5O5,repk1g28]  /. F[a___]:> F[28,{a}]


% - (% /. Den[___]->0) /. a_ Den[b___]-> Den[b]


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/G28/group28O5O5.m",exp4fire1group28O5O5]


exp4firegroup28totalO5O5=Total[exp4fire1group28O5O5 ]//. 
{Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]} /. Dcoeff[0,0,0,0]->0;


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/group28totalO5O5.m",exp4firegroup28totalO5O5]


exp4firegroup28onlyintsO5O5 = Union[List@@Plus[ Expand[exp4firegroup28totalO5O5] //.
a_ *F[b___]->F[b]]]  


Export["/home/users/moos/BSGamma/lm/Mathematica/REMASTEREDDiagrams/topclass28O5O5.m",exp4firegroup28onlyintsO5O5]


Union[exp4firegroup28onlyints,exp4firegroup28onlyintsO3O5,exp4firegroup28onlyintsO5O3,exp4firegroup28onlyintsO5O5]//Length


(* ::Section::Closed:: *)
(*diags only *)


(* ::Subsection:: *)
(*diag21*)


diagslist176fin=Import["~/BSGamma/lm/Mathematica/All176DiagramsBeforeIBP.m"];
gnum=21;
invsg21={{1,(k1)^2},{2,(p1)^2},{3,p2^2},{4,p3^2},{5,(pb-p1-p2-p3)^2},{6,(k1-p1-p2-p3)^2-mb2},{7,(k1-p1)^2},{8,(k1-pb)^2-mb2},{9,(k1-p3)^2},{10,(pb-p2-p3)^2},{11,(+p1+p2-pb)^2},{12,(p1+p3)^2},{13,(p1+p2+p3)^2-z},{14,(p2+p3)^2}};
props21=Table[ToExpression["invsg"<>ToString[gnum]][[i,2]],{i,1,14}]
ToExpression["invsg"<>ToString[gnum]] // TableForm


repk1g21 = {q4->pb-q1-q2-q3, s[a___,k1,b___]->s[a,kp1,b], Den[a___,{q1+q2+q3,mb},b___]->Den[a,b]*1/(z-mb2), Den[a___,-k1+c_,b___]->Den[a,k1-c,b],Den[a___,{-k1+c_,mb},b___]->Den[a,{k1-c,mb},b],
			(* Replacement of the denominators *)
			Den[a___,k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b], Den[a___,-k1,b___]->F[1,1,1,1,1,0,0,0,0,0,0,0,1,0]*Den[a,b] ,
			Den[a___,{k1-q1-q2-q3,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6+1,a7,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7+1,a8,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,{k1-pb,mb},b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8+1,a9,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,k1-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9+1,a10,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q2-q3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10+1,a11,a12,a13,a14]*Den[a,b],
			Den[a___,pb-q1-q2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]->F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11+1,a12,a13,a14]*Den[a,b],
			(* Replacements of the linear dependent invariants *)
			s[a___,24,b___]-> mb2*s[a,b]-s[a,12,b]-s[a,13,b]-s[a,14,b]-s[a,23,b]-s[a,34,b], 
			s[a___,k4,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2*(F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8-1,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							(z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							mb2*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			(* Replacement of the numerators *)
			s[a___,23,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b],
			s[a___,12,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]+ 
																						  z*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3-1,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14-1]*s[a,b]+
																							F[a1,a2-1,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
																							F[a1,a2,a3,a4-1,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
																							F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,14,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10-1,a11,a12,a13,a14]*s[a,b],
			s[a___,13,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12-1,a13,a14]*s[a,b],
			s[a___,34,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11-1,a12,a13,a14]*s[a,b],
			s[a___,kp1,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]) ,
			s[a___,k2,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> 1/2 (F[a1,a2,a3,a4,a5,a6,a7-1,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1,a2,a3,a4,a5,a6-1,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                 F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                (z-mb2)*F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]+
                                                                                                 F[a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13-1,a14]*s[a,b]),
			s[a___,k3,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> -1/2 (F[a1,a2,a3,a4,a5,a6,a7,a8,a9-1,a10,a11,a12,a13,a14]*s[a,b]-
                                                                                                F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b]),
			s[a___,kk,b___]*F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_] :> F[a1-1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14]*s[a,b], 
			s[]->1, Den[]->1,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a13<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a2<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a3<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a4<=0 ,
			F[a1_,a2_,a3_,a4_,a5_,a6_,a7_,a8_,a9_,a10_,a11_,a12_,a13_,a14_]:>  0 /; a5<=0 };


diag21={diagslist176fin[[4*21]]} /. q4->pb-q1-q2-q3 /. Den[a___,{k1+pb,mb},c___,{k1+q1+q2+q3,mb},b___] :> (Den[a,{k1+pb,mb},c,{k1+q1+q2+q3,mb},b] /. k1->-k1)//. 
 {Den[a___,-k1+c_,b___] :> Den[a,k1-c,b], Den[a___,{-k1+c_,mb},b___] :> Den[a,{k1-c,mb},b],Den[a___,k1+q1,b___] :> (Den[a,k1+q1,b] /. k1 :>   -k1 )} ;


tab[group_,rule_] := Table[Collect[
Expand[Expand[Expand[group[[i]] //. rule] //.rule ] //. rule ] //.rule ,
 _F,Simplify],{i,1,Length[group]}];


exp4fire1group21 = tab[ToExpression["diag"<>ToString[gnum]],ToExpression["repk1g"<>ToString[gnum]]]


% - (% /. Den[___]->0)
%% - (%% /. s[___]->0)


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/onebyone/diag"<>ToString[gnum]<>".m",ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]]


exp4firegroup21total=Total[ToExpression["exp4fire1group"<>ToString[gnum]] /. F[a___]:> F[gnum,{a}]] //. {Dcoeff[a1_,a2_,a3_,a4_]-Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1-b1,a2-b2,a3-b3,a4-b4],Dcoeff[a1_,a2_,a3_,a4_]+Dcoeff[b1_,b2_,b3_,b4_] :> Dcoeff[a1+b1,a2+b2,a3+b3,a4+b4]};


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/onebyone/diag"<>ToString[gnum]<>"total.m",Total[ToExpression["exp4firegroup"<>ToString[gnum]<>"total"] /. F[a___]:> F[gnum,{a}]]]


exp4firediag21onlyints = Union[List@@Plus[ Expand[Total[ToExpression["exp4fire1group"<>ToString[gnum]]] //.
a_ *F[b___]->F[b]]]]  /. F[b___]->{gnum,{b}}


Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/onebyone/ints"<>ToString[gnum]<>".m",ToExpression["exp4firediag"<>ToString[gnum]<>"onlyints"]]


(* ::Subsubsection:: *)
(*Creation of the .start file*)


Get["/home/users/moos/Programme/fire/FIRE6/FIRE6.m"];
Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
RESTRICTIONS = {{0,-1,-1,-1,-1,0,0,0,0,0,0,0,-1,0},{0,-1,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,-1,0,0,0,0,0,0,0,0,0},{0,-1,-1,0,0,0,0,0,0,0,0,0,0,0},{0,-1,0,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,-1,-1,0,0,0,0,0,0,0,0,0},{0,0,-1,-1,0,0,0,0,0,0,0,0,0,0},{0,-1,0,0,0,0,0,0,0,0,0,0,0,0},{0,0,-1,0,0,0,0,0,0,0,0,0,0,0},{0,0,0,-1,0,0,0,0,0,0,0,0,0,0},{0,0,0,0,-1,0,0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0,0,0,0,0,-1,0}};
PrepareIBP[];
Prepare[];
SaveStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]];
Quit[];


(* ::Subsubsection:: *)
(*Loading the tables & putting in the Master integrals*)


SetDirectory["/home/users/moos/Programme/fire/FIRE6/"];
Get["FIRE6.m"];
LoadStart["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum],gnum];
Burn[];
LoadTables[{"/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/topclass"<>ToString[gnum]<>".tables"}];


Internal={k1,p1,p2,p3};
External={pb};
Propagators =ToExpression["props"<>ToString[gnum]];
MasterIntegrals[]
final21=Import["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/diags/group"<>ToString[gnum]<>"total.m"] 
final21minimalG =Collect[Expand[ ToExpression["final"<>ToString[gnum]] /.  FindRules[MasterIntegrals[]]],_G];
Export["/home/users/moos/Programme/fire/FIRE6/FourloopBSG/Reduction4Loop/afteribp/group"<>ToString[gnum]<>"afteribp.m",ToExpression["final"<>ToString[gnum]<>"minimalG"]]  


(* ::Section::Closed:: *)
(*FeynCalc PaVe*)


<<FeynCalc`;


fcmomenta= { Pair[Momentum[q1_, D], Momentum[q1_, D]] ->0,Pair[Momentum[q1, D], Momentum[q2, D]]->s12/2,Pair[Momentum[q1, D], Momentum[q3, D]]->s13/2,Pair[Momentum[q1, D], Momentum[q4, D]]->s14/2,
Pair[Momentum[q2, D], Momentum[q3, D]]->s23/2,Pair[Momentum[q2, D], Momentum[q4, D]]->s24/2,Pair[Momentum[q3, D], Momentum[q4, D]]->s34/2};
fcdens={FeynAmpDenominator[PropagatorDenominator[Momentum[q1, D] + Momentum[q4, D], 0]]->1/(s14/2),massDen[a_]->FAD[{a,mb}]};
invtosp = {k2 -> SPD[k1,k1],qk1->SPD[q1,k1],qk2->SPD[q2,k1],qk3->SPD[q3,k1],qk4->SPD[q4,k1]};
pv[diagpart_,loopmom_]:=TID[diagpart,loopmom];
den2inv = {Den[q2 + q4]-> s24^-1, Den[q3 + q4]->s34^-1, Den[q1 + q4]->s14^-1};


diag4 = Import["~/BSGamma/lm/OneLoopBSG4BodyO3O3uu.m"];


diagpretid=diag4 /. Den[a___,s[b___]]->FAD[a]s[b] /. s[a___,k1,b___]->SPD[k1,q1] /. s[a___,k2,b___]->SPD[k1,q2]/. s[a___,k3,b___]->SPD[k1,q3]/. s[a___,k4,b___]->SPD[k1,q4] /. s[a___,kk,b___]->SPD[k1,k1] 


Export["~/BSGamma/lm/OneLoopBSG4BodyO3O3uuPreTID.m",diagpretid]


diagpretid= Import["~/BSGamma/lm/OneLoopBSG4BodyO3O3uuPreTID.m"]


(* ::Subsubsection:: *)
(*Don't collect in B0 functions etc. easier to collect denominators of k*)


test=TID[diagpretid[[1]],k1]  //. { FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] + Momentum[q2_, D] + Momentum[q3_, D], mb_],b___]-> ((q1+q2+q3)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q3_, D] + Momentum[q4_, D], mb_],b___]:> ((q3+q4)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] - Momentum[q2_, D] - Momentum[q3_, D],mb_],b___]-> ((q1-q2-q3)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] - Momentum[q2_, D] ,mb_],b___]-> ((q1-q2)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D]  ,mb_],b___]-> ((q1)^2-mb^2)^-1 FeynAmpDenominator[a,b]} /. FeynAmpDenominator[]->1 //. (k1+a_)^-2->Kden[k+a]//. (k1)^-2->Kden[k] //. 
Kden[a___]*Kden[b___]-> Kden[a,b];
test
test//InputForm


(* ::Subsubsection:: *)
(*Map Tensorintegral reduction on the diags*)


diagaftertid=Map[pv[#,k1] & ,diagpretid] 


Export["~/BSGamma/lm/OneLoopBSG4BodyO3O3uuAfterTID.m",diagaftertid]


diagaftertid=Import["~/BSGamma/lm/OneLoopBSG4BodyO3O3uuAfterTID.m"];


(* ::Subsubsection:: *)
(*Sortieren der Terme*)


looplistproto=List@@Plus[diagaftertid]  /. fcmomenta //. FeynAmpDenominator[rest1___,PropagatorDenominator[p___, 0],rest2___]:> Den[p] FeynAmpDenominator[rest1,rest2] //.
 FeynAmpDenominator[rest1_,PropagatorDenominator[q1 + q2 + q3, mb],rest2_] ->(s14+s24+s34)^-1 FeynAmpDenominator[rest1,rest2] //. 
FeynAmpDenominator[rest1___,PropagatorDenominator[p___, mb],rest2___]:> MDen[p] FeynAmpDenominator[rest1,rest2]  //. Momentum[k_, D]->k  /. FeynAmpDenominator[]->1 //. den2inv /. {s12->1,s13->1,s14->1,s23->1,s24->1,s34->1} /. 
 Dcoeff[___]->1 /. s[___]->1 /. g[___]->1


(* ::Subsubsection:: *)
(*verschieden strukturen, die auftreten*)


llproto=List@@Plus[Total[diagaftertid]];


ll=llproto  /. fcmomenta //. FeynAmpDenominator[rest1___,PropagatorDenominator[p___, 0],rest2___]:> Den[p] FeynAmpDenominator[rest1,rest2] //.
 FeynAmpDenominator[rest1_,PropagatorDenominator[q1 + q2 + q3, mb],rest2_] ->(s14+s24+s34)^-1 FeynAmpDenominator[rest1,rest2] //. 
FeynAmpDenominator[rest1___,PropagatorDenominator[p___, mb],rest2___]:> MDen[p] FeynAmpDenominator[rest1,rest2]  //. Momentum[k_, D]->k  /. FeynAmpDenominator[]->1 //. den2inv /. {s12->1,s13->1,s14->1,s23->1,s24->1,s34->1} /. 
 Dcoeff[___]->1 /. s[___]->1 /. g[___]->1;


structures=Union[Union[List@@Plus[Total[Union[ll //. Den[a1__]Den[a2__]->Den[a1,a2] /. MDen[q1+q2+q3]->1 //. MDen[a1__]MDen[a2__]->MDen[a1,a2] //.
Times[a_Rational,Den[b___]]->Den[b] /.Times[a_Rational,MDen[b___]]->MDen[b]]]]]  /. a___ Den[a1___]*MDen[a2___]->Den[a1]MDen[a2] /.
Times[a_Integer,Den[b___]]->Den[b]  /. Times[d,Den[b___]]->Den[b]  /. Times[d^2,Den[b___]]->Den[b] /. Times[d^2,MDen[b___]]->MDen[b]];


Export["loopstructuresBSG.m",structures]


structures=Import["loopstructuresBSG.m"];


structures // TableForm


(* ::Subsubsection:: *)
(*koeffizienten einer bestimmten loopstruktur*)


Total[diagaftertid] /. fcmomenta //. FeynAmpDenominator[rest1___,PropagatorDenominator[p___, 0],rest2___]:> Den[p] FeynAmpDenominator[rest1,rest2] //.
 FeynAmpDenominator[rest1_,PropagatorDenominator[q1 + q2 + q3, mb],rest2_] ->(s14+s24+s34)^-1 FeynAmpDenominator[rest1,rest2] //. 
FeynAmpDenominator[rest1___,PropagatorDenominator[p___, mb],rest2___]:> MDen[p] FeynAmpDenominator[rest1,rest2]  //. Momentum[k_, D]->k  /. FeynAmpDenominator[]->1 //. den2inv //. 
Den[a1__]Den[a2__]->Den[a1,a2] /. MDen[q1+q2+q3]->1 //. MDen[a1__]MDen[a2__]->MDen[a1,a2]


coef1={structures[[1]],Coefficient[
Total[diagaftertid] /. fcmomenta //. FeynAmpDenominator[rest1___,PropagatorDenominator[p___, 0],rest2___]:> Den[p] FeynAmpDenominator[rest1,rest2] //.
 FeynAmpDenominator[rest1_,PropagatorDenominator[q1 + q2 + q3, mb],rest2_] ->(s14+s24+s34)^-1 FeynAmpDenominator[rest1,rest2] //. 
FeynAmpDenominator[rest1___,PropagatorDenominator[p___, mb],rest2___]:> MDen[p] FeynAmpDenominator[rest1,rest2]  //. Momentum[k_, D]->k  /. FeynAmpDenominator[]->1 //. den2inv //. 
Den[a1__]Den[a2__]->Den[a1,a2] /. MDen[q1+q2+q3]->1 //. MDen[a1__]MDen[a2__]->MDen[a1,a2]  ,
structures[[1]]] /. MDen[___]->0 /. Den[___]->0}


coef1fac=Factor/@Plus[coef1[[2]]] /. s12+s13+s14->s234m1 /. s13+s14->s34m1 /.  s12+s13->s23m1 /. s12+s14->s24m1


(* ::Subsubsection:: *)
(*find out which denominators occur*)


Together[coef1fac /. Dcoeff[___]->1]


struclist=Union[List@@Plus[Factor/@(coef1[[2]] /. Dcoeff[___]->1 /. g[___]->1 ) ]  /. Times[a_Integer,b_]->Times[b]  /. Times[Rational[a1_,a2_],b_]->Times[b]]


num[a_] := a /. Numerator[a]-> 1 


2/5 /. Rational[a_,b_]->Rational[1,b]


struclist


struclist //. {1/s12-> Den[inv12],1/s13-> Den[inv13],1/s14-> Den[inv14],1/s23-> Den[inv23],1/s24-> Den[inv24],1/s34-> Den[inv34],1/(s12+s13)-> Den[inv23m1],1/(s13+s14)-> Den[inv34m1],1/(s12+s14)-> Den[inv24m1],
1/(s12+s13+s14)-> Den[inv234m1], s14^a_-> Den[inv14]^-a, s24^a_-> Den[inv24]^-a, s34^a_-> Den[inv34]^-a} //. Den[a___]*Den[b___]->Den[a,b] //. {Den[a___]^2->Den[a,a],Den[a___]^3->Den[a,a,a]} /.
{s12->1,s13->1,s14-> 1,s23->1,s24->1,s34->1} // Union


% // Length


%110[[9]]  /. s14^a_-> Den[inv14]^-a


coef1[[2]] /. Dcoeff[___]->1 /. g[___]->1 


Together[%149]














diagaftertidcol= Collect[diagaftertidtot //. { FeynAmpDenominator[PropagatorDenominator[Momentum[q1, D] + Momentum[q2, D] + Momentum[q3, D], mb]]-> (-s14-s24-s34)^-1},_PaVe]


diaglist=List@@Plus[diagaftertidcol]


Collect[Expand[diaglist[[1]] //. { FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] + Momentum[q2_, D] + Momentum[q3_, D], mb_],b___]-> ((q1+q2+q3)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q3_, D] + Momentum[q4_, D], mb_],b___]->((q3+q4)^2-mb^2)^-1} /. FeynAmpDenominator[]->1 //. 
{(q1+q2+q3)^2->s12+s13+s23,mb^2->s12+s13+s14+s23+s24+s34,(q3+q4)^-2->s34^-1,(q2+q4)^-2->s24^-1,(q1+q4)^-2->s14^-1}  //. (-a_)->(a) //. {s12+s13+s23->s123,s14+s24+s34->s1234,s14/2+s24/2+s34/2->s1234/2} ] /. srep //. 
{1/s[a_]->Den[a],1/s[a_]^2->Den[a,a],1/s[a_]^3->Den[a,a,a]} //. 
Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]  //.{
 s[a___]*s[b___]->s[a,b], s[a___]^2*s[b___]^2->s[a,a,b,b] , s[a___]^2*s[b___]->s[a,a,b] , s[a___]^3*s[b___]->s[a,a,a,b]} /. Dcoeff[a1_,a2_,a3_,a4_]->a1+a2*d+a3*d^2+a4*d^3,{_PaVe,_Den _s},Simplify] 


diaglist[[2]] //. { FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] + Momentum[q2_, D] + Momentum[q3_, D], mb_],b___]-> ((q1+q2+q3)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q3_, D] + Momentum[q4_, D], mb_],b___]->((q3+q4)^2-mb^2)^-1} /. FeynAmpDenominator[]->1 


colsimp[diaglistpart_]:=Collect[Expand[Expand[Collect[Expand[diaglistpart //. { FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] + Momentum[q2_, D] + Momentum[q3_, D], mb_],b___]-> ((q1+q2+q3)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q3_, D] + Momentum[q4_, D], mb_],b___]->((q3+q4)^2-mb^2)^-1} /. FeynAmpDenominator[]->1 //. 
{(q1+q2+q3)^2->s12+s13+s23,mb^2->s12+s13+s14+s23+s24+s34,(q3+q4)^-2->s34^-1,(q2+q4)^-2->s24^-1,(q1+q4)^-2->s14^-1}  //. (-a_)->(a) ],
Dcoeff[___],Factor ] //. {s12+s13+s23->s123,s14+s24+s34->s1234,s13+s23+s34->s1243,s14/2+s24/2+s34/2->s1234/2} /. numrep ] //. 
{1/num[a_]->Den[a],1/(num[a1_]+num[a2_])->Den[a1+a2],1/num[a_]^2->Den[a,a],1/(num[a1_]+num[a2_])^2->Den[a1+a2]^2,1/num[a_]^3->Den[a,a,a]} //. 
Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]  //.{
 num[a___]*num[b___]->num[a,b], num[a___]^2*num[b___]^2->num[a,a,b,b] , num[a___]^2*num[b___]->num[a,a,b] , num[a___]^3*num[b___]->num[a,a,a,b], num[a___]^4*num[b___]->num[a,a,a,a,b]} /. Dcoeff[a1_,a2_,a3_,a4_]->a1+a2*d+a3*d^2+a4*d^3 ],
 {_PaVe,_Den _num},Simplify]


srep


numrep={s12->num[s12],s13->num[s13],s14->num[s14],s23->num[s23],s24->num[s24],s34-> num[s34],s123->num[s123],s1234->num[s1234],s1243->num[s1243]};


Collect[Expand[Expand[Collect[Expand[diaglist[[8]] //. { FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q1_, D] + Momentum[q2_, D] + Momentum[q3_, D], mb_],b___]-> ((q1+q2+q3)^2-mb^2)^-1 FeynAmpDenominator[a,b],
FeynAmpDenominator[a___,PropagatorDenominator[Momentum[q3_, D] + Momentum[q4_, D], mb_],b___]->((q3+q4)^2-mb^2)^-1} /. FeynAmpDenominator[]->1 //. 
{(q1+q2+q3)^2->s12+s13+s23,mb^2->s12+s13+s14+s23+s24+s34,(q3+q4)^-2->s34^-1,(q2+q4)^-2->s24^-1,(q1+q4)^-2->s14^-1}  //. (-a_)->(a) ],
Dcoeff[___],Factor ] //. {s12+s13+s23->s123,s14+s24+s34->s1234,s13+s23+s34->s1243,s14/2+s24/2+s34/2->s1234/2} /. numrep ] //. 
{1/num[a_]->Den[a],1/(num[a1_]+num[a2_])->Den[a1+a2],1/num[a_]^2->Den[a,a],1/(num[a1_]+num[a2_])^2->Den[a1+a2]^2,1/num[a_]^3->Den[a,a,a]} //. 
Den[a___]*Den[b___]->Den[a,b] //. Den[a___]^2*Den[b___]->Den[a,a,b] //. Den[a___]^3*Den[b___]->Den[a,a,a,b]  //.{
 num[a___]*num[b___]->num[a,b], num[a___]^2*num[b___]^2->num[a,a,b,b] , num[a___]^4*num[b___]^2->num[a,a,a,a,b,b], num[a___]^2*num[b___]->num[a,a,b] , num[a___]^3*num[b___]->num[a,a,a,b], num[a___]^4*num[b___]->num[a,a,a,a,b]} /.
  Dcoeff[a1_,a2_,a3_,a4_]->a1+a2*d+a3*d^2+a4*d^3 ],{_PaVe,_Den _num}] 


 


diaglist /. PaVe[a___]*b_->PaVe[a] /. s12+s13+s14+s23+s24+s34-> p1234^2 /. s12+s13+s23->s123 /. s23+s24+s34-> s234 /. s13+s14+s34->s134 /. s12+s14+s24->s124 


%172[[4]]


Solve[y^2==(p1+p2)^2&&(x-z)^2==(p1+p4)^2 && (x-y)^2==(p1+p2+p4)^2,{x,y,z}] 


diaglist[[9]]


diagssimp = Map[colsimp,Take[diaglist,{1,10}]]


(* ::Section::Closed:: *)
(*Integration of Kernel in proceedings (4.10)*)


(* ::Text:: *)
(*rules for the hypergeometrics and beta-functions:*)


hypergeoinvarg = { Hypergeometric2F1[a1_,a2_,a3_,-(z_/(1-z_))]-> (1-z)^a1 Hypergeometric2F1[a1,a3-a2,a3,z]};
betatogamma = {Beta[a_,b_]->Gamma[a]Gamma[b]/Gamma[a+b]};
barback ={zbar->1-z,xbar->1-x,vbar->1-v,wbar->1-w,ubar->1-u};


prepare[var_] := {(-1+var)^a1_->(-1)^a1 (1-var)^a1,ToExpression[ToString[var]<>"bar"] -> 1-var ,(a_-b_ var)^c_->a^c (1-b/a var)^c,(a_+b_ var)^c_->a^c (1+b/a var)^c};
beta[var_] := {(1-var)^a2_ var^a1_->Beta[1+a1,1+a2]};
factor = {(a_+a_*c_)^b_  :>  (a)^b (1+c)^b};
hyp[var_] := {(1-var)^a2_ var^a1_ (1+var a_)^a3_->Gamma[a2+1]Gamma[a1+1]/Gamma[a2+a1+2]   Hypergeometric2F1[1+a1,-a3,2+a1+a2,-a]}


(* ::Text:: *)
(*kernel and determinant:*)


origkern= (s13*s24)/s34 * (s23+s34+s24)^-\[Epsilon];
kern=(s23*s14)/s24 * (s12+s24+s14)^-\[Epsilon];
determinante=4^(-2 \[Epsilon]) (u ubar)^(-(1/2)-\[Epsilon]) v^(1-2 \[Epsilon]) vbar^-\[Epsilon] w^-\[Epsilon] wbar^-\[Epsilon] x^-\[Epsilon] xbar^-\[Epsilon] z zbar (z zbar)^(-2 \[Epsilon]);
Nd4body=(2^(8-5D) Pi^(1-(3D)/2) mb^(3D-9))/(4 Nc Gamma[(D-1)/2]Gamma[(D-2)/2]Gamma[(D-3)/2]);


varchange={s12->v w z,s34->vbar zbar,s14->v x zbar,s23->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2 Sqrt[vbar w wbar x xbar]) z};
deltas= {s24 -> zbar -s14-s34, s13 -> z-s12-s23};


kernel=determinante*kern  /. deltas /. varchange //PowerExpand;


(* ::Text:: *)
(*integrations:*)


uint=Expand[PowerExpand[kernel]] /. barback //. factor //. prepare[u] /. hyp[u] /. beta[u];


vint = PowerExpand[Expand[uint]]//. (a_)^b_  :>  (Simplify[a])^b   //. factor  //. prepare[v]  /. hyp[v] /. beta[v];


xint = PowerExpand[Expand[vint]]//. (a_)^b_  :>  (Simplify[a])^b   //. factor  //. prepare[x] /. hyp2[x] /. beta[x];


wint =PowerExpand[Expand[xint]] //. (a_)^b_  :>  (Simplify[a])^b //. (a_)^b_  :>  (Expand[a])^b   //. factor  //. prepare[w] /. hyp2[w] /. beta[w]


Collect[wint /. hypergeoinvarg  ,_Hypergeometric2F1,FullSimplify]


(* ::Section:: *)
(*Integration of Test-Kernel [with(out) IBP/PaVe] (s13 s24 k.p1 k.p3)/(s34 k^2(k+p2+p3+p4)^2)*)


(* ::Text:: *)
(*rules for the hypergeometrics and beta-functions*)


hypergeoinvarg = { Hypergeometric2F1[a1_,a2_,a3_,-(z_/(1-z_))]-> (1-z)^a1 Hypergeometric2F1[a1,a3-a2,a3,z]};
betatogamma = {Beta[a_,b_]->Gamma[a]Gamma[b]/Gamma[a+b]};
barback ={zbar->1-z,xbar->1-x,vbar->1-v,wbar->1-w,ubar->1-u};
prepare[var_] := {(-1+var)^a1_->(-1)^a1 (1-var)^a1,ToExpression[ToString[var]<>"bar"] -> 1-var ,(a_-b_ var)^c_->a^c (1-b/a var)^c,(a_+b_ var)^c_->a^c (1+b/a var)^c};
beta[var_] := {(1-var)^a2_ var^a1_->Beta[1+a1,1+a2]};
factor = {(a_+a_*c_)^b_  :>  (a)^b (1+c)^b};
hyp[var_] := {(1-var)^a2_ var^a1_ (1+var a_)^a3_->Gamma[a2+1]Gamma[a1+1]/Gamma[a2+a1+2]   Hypergeometric2F1[1+a1,-a3,2+a1+a2,-a]}


(* ::Text:: *)
(*kernel and determinant:*)


origkern= (s13*s24)/s34 * (s23+s34+s24)^-\[Epsilon];
kern=(s23 s14)/s24 s23 (s12+s24+s14)^(1-\[Epsilon]);
determinante=4^(-2 \[Epsilon]) (u ubar)^(-(1/2)-\[Epsilon]) v^(1-2 \[Epsilon]) vbar^-\[Epsilon] w^-\[Epsilon] wbar^-\[Epsilon] x^-\[Epsilon] xbar^-\[Epsilon] z zbar (z zbar)^(-2 \[Epsilon]);
Nd4body=(2^(8-5D) Pi^(1-(3D)/2) mb^(3D-9))/(4 Nc Gamma[(D-1)/2]Gamma[(D-2)/2]Gamma[(D-3)/2]);
varchange={s12->v w z,s34->vbar zbar,s14->v x zbar,s23->4 u Sqrt[vbar w wbar x xbar] z+(vbar w x+wbar xbar-2 Sqrt[vbar w wbar x xbar]) z};
deltas= {s24 -> zbar -s14-s34, s13 -> z-s12-s23};


kernel=determinante*kern  /. deltas /. varchange //PowerExpand;


(* ::Text:: *)
(*integrations:*)


uint=Expand[PowerExpand[kernel]] /. barback //. factor //. prepare[u] /. hyp[u] /. beta[u];


vint = PowerExpand[Expand[uint]]//. (a_)^b_  :>  (Simplify[a])^b   //. factor  //. prepare[v]  /. hyp[v] /. beta[v];


xint = PowerExpand[Expand[vint]]//. (a_)^b_  :>  (Simplify[a])^b   //. factor  //. prepare[x] /. hyp[x] /. beta[x];


wint =PowerExpand[Expand[xint]] //. (a_)^b_  :>  (Simplify[a])^b //. (a_)^b_  :>  (Expand[a])^b   //. factor  //. prepare[w] /. hyp[w] /. beta[w];


Collect[wint /. hypergeoinvarg  ,_Hypergeometric2F1,FullSimplify]


(* ::Section:: *)
(*Renaming of momenta for integral families*)


Flatten[{group30,group301,group24,group241,group27,group271,group22,group221,group21,group211,group28,group281,group31,group311,group25,group251}] //Length
