Symbol d;
Dimension d;
Functions hel,B,U,S,b,bbar,s,sbar,u,ubar,li,
photon,gab,f,cvx,pp,ppc,v,ev,vp,bar,mass,G1,G2(a);
CFunctions ga,pol,vrtx,prop2,p,prop,den,ga1,ga2,ga1b,ga2b,ga1five,ga2five,hf,
eps(a),eps1(a),eps2(a),eta(s),sym,asym,epssign,tr,massden;
Indices mu,nu,rho,sig,photind1,...,photind10,mu1,...,mu100,dum1,...,dum32,five;
Symbol k,N,i,a1,...,a100,n1,n2,n3,n4,mb,mb2,s12,s13,s14,s23,s24,s34,mark1,...,mark50,asbar,ab,au,aubar,
qk1,...,qk4,eps134k,eps234k,eps124k,eps123k,eps1234,Qu,Qs,Qb,Qubar,mom,e;
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
#include- NDR.h


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
* pinguin structure (sbar-b)(ubar-u)

id  vrtx(sbar(asbar?,psbar?),u(au?,pu?),ubar(aubar?,pubar?),b(ab?,pb?)) = vrtx(sbar(asbar,psbar),b(ab,pb))*vrtx(ubar(aubar,pubar),u(au,pu));

id  vrtx(ubar(aubar?,pubar?),u(au?,pu?)) = ga(aubar,Ouu,au);
id  vrtx(sbar(asbar?,psbar?),b(ab?,pb?)) = ga(asbar,Osb,ab);


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
* assign number to the lines with b and u respectively
*
if (occurs(Osb)=1);
id,once ga(?a1)=ga2(?a1);
endif;
if (occurs(Ouu)=1);
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
* ((-1)**`nphot') takes care of the pol(p)*pol(p)=-g_mu_nu
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

.sort

* "unpack" lorentz-index of photon
repeat;
id ga?(?a1,li(mu1?),?a3)=ga(?a1,mu1,?a3);
endrepeat;

*
* Insertion for the photon vertex
*

* u-quark
id ga1(u(q1?),?mu1,photind1,?mu2,Ouu,?mu3,ubar(p2?))=-i*Qu*ga1(u(q1),?mu1,photind1,?mu2,Ouu,?mu3,ubar(p2));
id ga1b(bar(ubar(q1?)),?mu1,bar(Ouu),?mu2,photind1,?mu3,bar(u(p2?)))=i*Qu*ga1b(bar(ubar(q1)),?mu1,bar(Ouu),?mu2,photind1,?mu3,bar(u(p2)));


* ubar-quark
id ga1(u(q1?),?mu1,Ouu,?mu2,photind1,?mu3,ubar(p2?))=-i*Qu*ga1(u(q1),?mu1,Ouu,?mu2,photind1,?mu3,ubar(p2));
id ga1b(bar(ubar(q1?)),?mu1,photind1,?mu2,bar(Ouu),?mu3,bar(u(p2?)))=i*Qu*ga1b(bar(ubar(q1)),?mu1,photind1,?mu2,bar(Ouu),?mu3,bar(u(p2)));

* s-quark
id ga2(s(q1?),?mu1,photind1,?mu2,Osb,?mu3,b(p2?))=-i*Qs*ga2(s(q1),?mu1,photind1,?mu2,Osb,?mu3,b(p2));
id ga2b(bar(b(q1?)),?mu1,bar(Osb),?mu2,photind1,?mu3,bar(s(p2?)))=i*Qs*ga2b(bar(b(q1)),?mu1,bar(Osb),?mu2,photind1,?mu3,bar(s(p2)));


* b-quark
id ga2(s(q1?),?mu1,Osb,?mu2,photind1,?mu3,b(p2?))=-i*Qb*ga2(s(q1),?mu1,Osb,?mu2,photind1,?mu3,b(p2));
id ga2b(bar(b(q1?)),?mu1,photind1,?mu2,bar(Osb),?mu3,bar(s(p2?)))=i*Qb*ga2b(bar(b(q1)),?mu1,photind1,?mu2,bar(Osb),?mu3,bar(s(p2)));




*
* replace prop(q,p) by p
* for massive quarks, use massden (here only one for the mb)
*
repeat;
id ga1(?a1,prop(b(p1?)),?a2)=i*massden(p1)*(ga1(?a1,p1,?a2)+mark1*mass(b)*ga1(?a1,?a2));
id ga1b(?a1,prop(b(p1?)),?a2)=-i*massden(p1)*(ga1b(?a1,p1,?a2)+mark2*mass(b)*ga1b(?a1,?a2));
id ga2(?a1,prop(b(p1?)),?a2)=i*massden(p1)*(ga2(?a1,p1,?a2)+mark3*mass(b)*ga2(?a1,?a2));
id ga2b(?a1,prop(b(p1?)),?a2)=-i*massden(p1)*(ga2b(?a1,p1,?a2)+mark4*mass(b)*ga2b(?a1,?a2));
endrepeat;

* flow vs. momentum for ubar (already right from QGRAF!)
*repeat;
*id ga1(?a1,prop(u(p1?)),bar(Ouu),?a2)=mom*i*den(p1)*ga1(?a1,p1,bar(Ouu),?a2);
*id ga1b(?a1,prop(u(p1?)),bar(Ouu),?a2)=-mom*i*den(p1)*ga1b(?a1,p1,bar(Ouu),?a2);
*id ga2(?a1,prop(u(p1?)),bar(Ouu),?a2)=mom*i*den(p1)*ga2(?a1,p1,bar(Ouu),?a2);
*id ga2b(?a1,prop(u(p1?)),bar(Ouu),?a2)=-mom*i*den(p1)*ga2b(?a1,p1,bar(Ouu),?a2);
*endrepeat;

* is right in QGRAF!
*id mom=1;

repeat;
id ga1(?a1,prop(b?(p1?)),?a2)=i*den(p1)*(ga1(?a1,p1,?a2)+mark1*mass(b)*ga1(?a1,?a2));
id ga1b(?a1,prop(b?(p1?)),?a2)=-i*den(p1)*(ga1b(?a1,p1,?a2)+mark2*mass(b)*ga1b(?a1,?a2));
id ga2(?a1,prop(b?(p1?)),?a2)=i*den(p1)*(ga2(?a1,p1,?a2)+mark3*mass(b)*ga2(?a1,?a2));
id ga2b(?a1,prop(b?(p1?)),?a2)=-i*den(p1)*(ga2b(?a1,p1,?a2)+mark4*mass(b)*ga2b(?a1,?a2));
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

id ga1?(?a1,bar(Ouu),?a2)=ga1(?a1,Ouuc,?a2);
id ga1?(?a1,bar(Osb),?a2)=ga1(?a1,Osbc,?a2);


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

.sort
chainout ga1;
id ga1(Ouu) = ga1(mu);
id ga1(Ouuc) = ga1(nu);
chainin ga1;
.sort
chainout ga2;
id ga2(Osb) = 1/2*(ga2(mu)-ga2(mu,five));
id ga2(Osbc) = 1/2*(ga2(nu)+ga2(five,nu));
chainin ga2;



* Using the NDR-Scheme for the treatment of gamma_5:


.sort
#do j=1,4
#do i=1,4
Local D'j''i'treeNDR= D'j''i'tree;
#enddo
#enddo

.sort
#do j=1,4
#do i=1,4
Hide D'j''i'tree;
#enddo
#enddo

.sort

#call NDR

.sort
*id ga1(?mu1,five,?mu2)=ga1five(?mu2,?mu1,five);
*id ga2(?mu1,five,?mu2)=ga2five(?mu2,?mu1,five);

*id ga1five?(mu1?,...,mu5?)=ga1five(mu1,...,mu5);
*id ga1five?(mu1?,...,mu6?)=ga1five(mu1,...,mu6);
*id ga1five?(mu1?,...,mu7?)=ga1five(mu1,...,mu7);
*id ga1five?(mu1?,...,mu8?)=ga1five(mu1,...,mu8);
*id ga1five?(mu1?,...,mu9?)=ga1five(mu1,...,mu9);
*id ga1five?(mu1?,...,mu11?)=ga1five(mu1,...,mu11);




*id ga1five(?mu1,five,?mu2)=ga1five(?mu2,?mu1,five);
*id ga2five(?mu1,five,?mu2)=ga2five(?mu2,?mu1,five);
*id ga2five(?mu1,p1,?mu6,five)=ga2five(?mu1,q1,?mu6,five)+ga2five(?mu1,q2,?mu6,five)+ga2five(?mu1,q3,?mu6,five)+ga2five(?mu1,q4,?mu6,five);

repeat;
*id ga2five(?mu1,mu2?,mu2?,?mu4,five)=d*ga2five(?mu1,?mu4,five);
*id ga2five(?mu1,mu2?,mu3?,mu2?,?mu4,five)=(2-d)*ga2five(?mu1,mu3,?mu4,five);
*id ga2five(?mu1,mu2?,mu3?,mu4?,mu2?,?mu5,five)=2*ga2five(?mu1,mu4,mu3,?mu5,five)+(d-2)*ga2five(?mu1,mu3,mu4,?mu5,five);
*id ga2five(?mu1,mu2?,nu?,rho?,sig?,mu2?,?mu6,five)=2*ga2five(?mu1,rho,sig,nu,?mu6,five)-2*ga2five(?mu1,nu,sig,rho,?mu6,five)-(d-2)*ga2five(?mu1,nu,rho,sig,?mu6,five);
*id ga2five(?mu1,q1?,q1?,?mu6,five)=0;
*id ga2five(mu2?,mu10?,mu11?,mu12?,mu2?,?mu6,five)=2*ga2five(mu10,mu11,mu12,?mu6,five)-2*ga2five(mu10,mu11,mu12,?mu6,five)-(d-2)*ga2five(mu10,mu11,mu12,?mu6,five);
endrepeat;



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

.sort
id ga2five(?mu1,p1,?mu6,five)=ga2five(?mu1,q1,?mu6,five)+ga2five(?mu1,q2,?mu6,five)+ga2five(?mu1,q3,?mu6,five)+ga2five(?mu1,q4,?mu6,five);
repeat;
id ga2five(?mu1,mu2?,mu2?,?mu4,five)=d*ga2five(?mu1,?mu4,five);
id ga2five(?mu1,mu2?,mu3?,mu2?,?mu4,five)=(2-d)*ga2five(?mu1,mu3,?mu4,five);
id ga2five(?mu1,mu2?,mu3?,mu4?,mu2?,?mu5,five)=2*ga2five(?mu1,mu4,mu3,?mu5,five)+(d-2)*ga2five(?mu1,mu3,mu4,?mu5,five);
id ga2five(?mu1,mu2?,nu?,rho?,sig?,mu2?,?mu6,five)=2*ga2five(?mu1,rho,sig,nu,?mu6,five)-
2*ga2five(?mu1,nu,sig,rho,?mu6,five)-(d-2)*ga2five(?mu1,nu,rho,sig,?mu6,five);
id ga2five(?mu1,q1?,q1?,?mu6,five)=0;
id ga2five(mu2?,mu10?,mu11?,mu12?,mu2?,?mu6,five)=2*ga2five(mu10,mu11,mu12,?mu6,five)-
2*ga2five(mu10,mu11,mu12,?mu6,five)-(d-2)*ga2five(mu10,mu11,mu12,?mu6,five);
endrepeat;

.sort
repeat;
id ga2five(?mu1,q1?,q2?,q1?,?mu4,five)=2*(q1.q2)*ga2five(?mu1,q1,?mu4,five);
id ga2five(?mu1,q1?,q2?,q3?,q1?,?mu4,five)=2*(q1.q2)*ga2five(?mu1,q1,q2,?mu4,five)-2*(q1.q3)*ga2five(?mu1,q1,q3,?mu4,five);
endrepeat;

.sort
id ga2five(mu1?,five)=0;
id ga2five(mu1?,mu2?,five)=0;
id ga2five(mu1?,mu2?,mu3?,five)=0;

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

.sort
id mark3=1;
id mark4=1;
id mark6=1;
id ga2five(?a1)=0;

Bracket den,massden,Qs,Qb,Qu,Qubar;



Print +s;
.end
