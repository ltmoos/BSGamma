Symbol d;
Dimension d;
Functions hel,B,U,S,b,bbar,s,sbar,u,ubar,li,
photon,gab,f,cvx,pp,ppc,v,ev,vp,bar,mass,G1,G2(a);
CFunctions ga,pol,vrtx,prop2,p,prop,den,ga1,ga2,ga1b,ga2b,ga2five,hf,eps(a),eps1(a),eps2(a),eta(s),sym,asym,epssign;
Indices mu,nu,rho,photind1,...,photind10,mu1,...,mu100,dum1,...,dum32,five;
Symbol k,N,i,a1,...,a100,n1,n2,n3,n4,mb,mb2,s12,s13,s14,s23,s24,s34,mark1,...,mark50,asbar,ab,au,aubar,qk1,...,qk4,eps134k,eps234k,eps124k,eps123k,eps1234;
Vectors p1,...,p10,q1,...,q10,q14,q24,q34,q123,pu,pubar,ps,psbar,pb,pbbar,k1,...,k4;
Tensor O1,O,O1c,Obu,Osu,Obuc,Osuc,Ouu,Ouuc,Osb,Osbc,Oub,Osu,Oubc,Osuc;
Off Statistics;

* Diagrams from QGRAF
#include- all3vertxNEWvrtx.h;


* Conjugation Routine
#include- conjugate.h;

* Routines for the Product of Eps*Eps, simplification of eta*eta and the
* Traces from FeynCalc
#include- ProdTwoEps_eps_eta.h;
#include- etasimp.h
#include- Larin.h


* Kinematics relevant for the process:

#include- KinematicsBSG4Body.h;



* define number of photons and gluons in the process

#define nphot "1"
#define nglu "0"

* specify the momenta of the photons (used to assign the indices photindi)

#define pphot1 "q4"

*
* split 4-vertex in 2 2-vertices and give them dirac structure
* create ga() as prototype to be converted to g_
*

* resolve the 4-vertex into the
* current-current structure (sbar-u)(ubar-b)

id  vrtx(sbar(asbar?,psbar?),u(au?,pu?),ubar(aubar?,pubar?),b(ab?,pb?)) =
vrtx(sbar(asbar,psbar),u(au,pu))*vrtx(ubar(aubar,pubar),b(ab,pb));


id  vrtx(ubar(aubar?,pubar?),b(ab?,pb?)) = ga(aubar,Oub,ab);
id  vrtx(sbar(asbar?,psbar?),u(au?,pu?)) = ga(asbar,Osu,au);


id prop(f?(a1?,p1?))=prop2(f(a1,a1+1,p1));

*
* put spinors and propagators in ga-functions
* CHECK the sign vs. flow parts!!!
*

.sort
repeat;
id ga(?a1,O?,a2?)*prop2(s?(a3?,a2?,p1?))=mark13*ga(?a1,O,prop(s(p1)),a3);
id pol(photon(n1?,p1?))=p(li(n1),p1);
id pol(b?(n1?,p1?))*ga(n1?,?a2)=ga(b(p1),?a2);
id pol(b?(n1?,p1?))*ga(?a2,n1?)=ga(?a2,b(p1));
id ga(?a1,a2?)*prop2(u?(a2?,a3?,p1?))=ga(?a1,prop(u(p1)),a3);
id ga(a1?,?a2)*prop2(u?(a3?,a1?,p1?))=ga(a3,prop(u(p1)),?a2);

id ga(a1?,?a2)*prop2(u?(a1?,a3?,p1?))=mark10*ga(a3,prop(u(p1)),?a2); *(?SIGN?)
#do i=1,`nphot'
id ga(?a1,a2?)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),photon(a4?,-`pphot`i''))=
ga(?a1,li(photind`i'),a3);
id ga(a1?,?a2)*vrtx(ubar?(a3?, p1?),u?(a1?,p2?),photon(a4?,-`pphot`i''))=
ga(a3,li(photind`i'),?a2);
id ga(a2?,?a1)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),photon(a4?,-`pphot`i''))=
mark11*ga(a3,li(photind`i'),?a1); *(?SIGN?)
id ga(?a1,a2?)*vrtx(ubar?(a3?, p1?),u?(a2?,p2?),photon(a4?,-`pphot`i''))=
mark12*ga(?a1,li(photind`i'),a3); *(?SIGN?)
#enddo
endrepeat;

*
* assign a photind to each respective photon
*





.sort
*
* assign number to the lines with b and s respectively
*
if (occurs(Oub)=1);
id,once ga(?a1)=ga2(?a1);
endif;
if (occurs(Osu)=1);
id,once ga(?a1)=ga1(?a1);
endif;

*
* Conjugate the Diagrams Di-> DiC
*

.sort
Hide D1tree,D2tree,D3tree,D4tree;

#call conj;

.sort
Unhide D1tree,D2tree,D3tree,D4tree;


*
* define the squared MEs:
* ((-1)**`nphot') takes care of the eps*eps=-g_mu_nu
*

.sort
#do j=1,4
#do i=1,4
Local D'j''i'tree = ((-1)**`nphot')*D'j'tree*D'i'treeC;
#enddo
#enddo


.sort
#do i=1,4
Hide D'i'tree,D'i'treeC;
#enddo



*
* replace prop(q,p) by p
*
repeat;
id ga1(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga1(?a1,p1,?a2)+mark1*mass(b)*ga1(?a1,?a2));

id ga1b(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga1b(?a1,p1,?a2)+mark2*mass(b)*ga1b(?a1,?a2));

id ga2(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga2(?a1,p1,?a2)+mark3*mass(b)*ga2(?a1,?a2));

id ga2b(?a1,prop(b?(p1?)),?a2)=den(p1)*(ga2b(?a1,p1,?a2)+mark4*mass(b)*ga2b(?a1,?a2));
endrepeat;

*
* use spin sum: hel(X)= X*Xbar
* multiplied by factor from averaged spin sum (1/2 for incoming, 1 for outgoing)
*

repeat;
id ga1(s?(p2?),?a2,b?(p1?))*ga1b(bar(b?(p1?)),?a4,bar(s?(p2?)))=
hf(b)*hf(s)*ga1(?a2,hel(b(p1)),?a4,hel(s(p2)));

id ga2(s?(p2?),?a2,b?(p1?))*ga2b(bar(b?(p1?)),?a4,bar(s?(p2?)))=
hf(b)*hf(s)*ga2(?a2,hel(b(p1)),?a4,hel(s(p2)));
endrepeat;

*
* operators-bar = Oc
*

id ga1(?a1,bar(Oub),?a2)=ga1(?a1,Osuc,?a2);
id ga1(?a1,bar(Osu),?a2)=ga1(?a1,Oubc,?a2);
id ga2(?a1,bar(Osu),?a2)=ga2(?a1,Osuc,?a2);
id ga2(?a1,bar(Oub),?a2)=ga2(?a1,Oubc,?a2);

*
* replace ubar*u=hel(u) by p_u-m_u (factors 1/2 missing for spin sum)
* (in massless case sign doesnt play role, BUT has to be adapted if mu,ms !=0)
*
repeat;
id ga1(?a1,hel(f?(p1?)),?a2)=ga1(?a1,p1,?a2)+mark5*mass(f)*ga1(?a1,?a2);
id ga2(?a1,hel(f?(p1?)),?a2)=ga2(?a1,p1,?a2)+mark6*mass(f)*ga2(?a1,?a2);
endrepeat;

*
* massless outgoing fermions s and u:
*
.sort
repeat;
id mass(b)^2=mb2;
endrepeat;
repeat;
id mass(s)=0;
id mass(u)=0;
id mass(ubar)=0;
endrepeat;



* "unpack" lorentz-index of photon
repeat;
id ga?(?a1,li(mu1?),?a3)=ga(?a1,mu1,?a3);
endrepeat;

id p(?a1)=1;
id hf(u)=1;
id hf(ubar)=1;
id hf(s)=1;
id hf(b)=1/2;


* make ga1,2 from CF to F to use chainout
.sort
Function ga1,ga2;

*
* convert ga to dirac chains
*
* put in mu*PL and PR*mu
*

chainout ga1;
chainout ga2;
.sort
id ga1?(Oub) = 1/2*(ga1(mu)-ga1(mu,five));
id ga1?(Oubc) = 1/2*(ga1(nu)+ga1(five,nu));
id ga2?(Osu) = 1/2*(ga2(mu)-ga2(mu,five));
id ga2?(Osuc) = 1/2*(ga2(nu)+ga2(five,nu));
chainin ga1;
chainin ga2;



* Using the Larin-Scheme for the treatment of gamma_5:


.sort
#do j=1,4
#do i=1,4
Local D'j''i'treeLarin= D'j''i'tree;
#enddo
#enddo

.sort
#do j=1,4
#do i=1,4
Hide D'j''i'tree;
*Hide D'j''i'treeLarin;
#enddo
#enddo
.sort
*Unhide D11treeLarin;

#call Larin

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


* simplify kinematical quantities:
.sort
#call Kin4body

*
* Simplify products of Epsilon-Tensors and the resulting metric tensors.
* First contract the EpsTens that come from the same line, then the mixed ones:
*
.sort
repeat;
#call EpsProd
#call Etasimp
endrepeat;
.sort
id eps1(mu1?,mu2?,mu3?,mu4?)=eps(mu1,mu2,mu3,mu4);
id eps2(mu1?,mu2?,mu3?,mu4?)=eps(mu1,mu2,mu3,mu4);
.sort
repeat;
#call EpsProd
#call Etasimp
endrepeat;

* Elimination of p1
.sort
id eps(p1,p2?,p3?,p4?)=eps(q1,p2,p3,p4)+eps(q2,p2,p3,p4)+eps(q3,p2,p3,p4)+eps(q4,p2,p3,p4);
.sort
repeat;
id eps(q2,q3,q4,k1)=eps234k;
id eps(q1,q3,q4,k1)=eps134k;
id eps(q1,q2,q4,k1)=eps124k;
id eps(q1,q2,q3,k1)=eps123k;
id eps(q1,q2,q3,q4)=eps1234;
endrepeat;

*
* Kinematics
*
.sort
#call Kin4body

id i^2=-1;

* larin-replace is -a1*eps

id p(?a1)=1;

id mark1=1;
id mark2=1;
id mark3=1;
id mark4=1;
id mark5=1;
id mark6=1;

Bracket den;

Print +s;
.end
