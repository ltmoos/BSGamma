Symbol d;
Dimension d;
Functions hel,B,U,S,b,bbar,s,sbar,u,ubar,li,
photon,gab,f,cvx,pp,ppc,v,ev,vp,bar,mass,G1,G2(a),g2five;
CFunctions ga,pol,vrtx,prop2,p,prop,den,ga1,ga2,ga1b,ga2b,ga2five,hf,eps(a),eps1(a),eps2(a),eta(s),sym,asym,epssign;
Indices mu,nu,rho,photind1,...,photind10,mu1,...,mu100,dum1,...,dum32,five;
Symbol k,N,i,a1,...,a100,n1,n2,n3,n4,mb,mb2,s12,s13,s14,s23,s24,s34,mark1,...,mark50,asbar,ab,au,aubar,qk1,...,qk4,eps134k,eps234k,eps124k,eps123k,eps1234;
Vectors p1,...,p10,q1,...,q10,q14,q24,q34,q123,pu,pubar,ps,psbar,pb,pbbar,k1,...,k4;
Tensor O1,O,O1c,Obu,Osu,Obuc,Osuc,Ouu,Ouuc,Osb,Osbc;
Off Statistics;



Local astest=ga1(mu1,...,mu4,five);


repeat;
id ga1(?a1,five)=distrib_(1,2,eta,g2five,?a1);
*id g2five(?a1)=ga1(?a1,five);
*id ga1(mu1?,mu2?,mu3?,mu4?,five)=eps;
endrepeat;



p +s;
.end
