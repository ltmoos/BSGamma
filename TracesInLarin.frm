Dimension d;
Functions hel,B,U,S,b,bbar,s,sbar,u,ubar,li,
photon,gab,f,cvx,pp,ppc,v,ev,vp,bar,mass,G1,G2(a);
CFunctions ga,pol,vrtx,prop2,p,prop,den,ga1,ga2,ga1b,ga2b,ga2five,hf,eps1(a),eps2(a),eps(a),eta(s),sym,asym;
Indices mu,nu,rho,sig,photind,mu1,...,mu100,dum1,...,dum10,five,al;
Symbol epssign,d,d1,k,N,i,a1,...,a100,n1,n2,n3,n4,mb,mb2    ,s12,s13,s14,s23,s24,s34,convfac1proj,mark1,mark2,mark3,mark4,mark5,mark6;
Vectors pp1,p1,...,p10,q1,q2,q3,q4,q,q14,q24,q34,q123,pu,pubar,ps,psbar,pb,pbbar;
Tensor O1,O,O1c,Obu,Osu,Obuc,Osuc,Ouu,Ouuc,Osb,Osbc;


#include- etasimp.h
#include- tracesNoG5.h;
#include- ProdTwoEps_eps_eta.h;


Local TR1= ga2(al,five,mu,nu,rho,al,nu,five,mu,rho);

Local TR1AC=-ga2(al,mu,nu,rho,al,nu,mu,rho);

Local TR1alterD= 2*ga2(al,five,mu,al,rho,five,mu,rho)+(d-2)*ga2(al,five,mu,rho,al,five,mu,rho);

Local TR1alter4= 2*ga2(al,five,mu,al,rho,five,mu,rho)+(4-2)*ga2(al,five,mu,rho,al,five,mu,rho);


Local TR2= ga2(al,five,nu,rho,al,nu,five,rho);

Local TR2alterD= 2* ga2(al,five,al,rho,five,rho)+(d-2)*ga2(al,five,rho,al,five,rho);

Local TR2alter4= 2* ga2(al,five,al,rho,five,rho)+(4-2)*ga2(al,five,rho,al,five,rho);

Local TR3= ga2(al,five,nu,al,nu,five);

Local TR3alterD= (2-d)*ga2(al,five,al,five);

Local TR3alter4= (2-4)*ga2(al,five,al,five);

Local TR4= ga2(al,five,nu,nu,al,five);

Local TR4alterD= d*ga2(al,five,al,five);

Local TR4alter4= d*ga2(al,five,al,five);

Local TR5= ga2(al,mu,nu,rho,sig,al,five);

Local TR6= ga2(al,mu,nu,rho,mu,al,five);

Local TR7= ga2(al,mu,nu,nu,mu,al,five);

Local TR8= ga2(al,five,mu,nu,rho,nu,al,five,mu,rho);

Local TR8alterD= (2-d)*ga2(al,five,mu,rho,al,five,mu,rho);

Local TR9= ga2(al,five,mu,nu,rho,mu,al,five,nu,rho);

Local TR9alterD=  2*ga2(al,five,rho,nu,al,five,nu,rho)+(d-2)* ga2(al,five,nu,rho,al,five,nu,rho);

Local TR10= ga2(mu3, mu11, mu4, mu5, mu4, mu7, mu9, mu11);

Local TR11= ga2(mu1,mu2,mu3,mu4,mu5,mu4,mu7,mu2,mu3,mu1);



id ga2?(?mu1,mu2?,five,?mu3,mu4?,five,?mu5)=i/6*i/6*eps(mu2,dum1,dum2,dum3)*eps(mu4,dum4,dum5,dum6)*ga2(?mu1,dum1,dum2,dum3,?mu3,dum4,dum5,dum6,?mu5);



id ga2(?mu1,mu2?,five,?mu3)=-i/6*eps(mu2,dum1,dum2,dum3)*
ga2(?mu1,dum1,dum2,dum3,?mu3);



.sort
chainout ga1;
repeat;
id ga1(mu1?)=g_(1,mu1);
endrepeat;
.sort
chainout ga2;
repeat;
id ga2(mu1?)=g_(2,mu1);
endrepeat;

.sort
Tracen,1;
.sort
Tracen,2;




#call Etasimp
#call EpsProd



*id d=4;
id i^2=-1;


p +s;
.end
