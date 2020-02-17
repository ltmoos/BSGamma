Functions hel,B,U,S,b,bbar,s,sbar,u,ubar,li,
photon,gab,f,cvx,pp,ppc,v,ev,vp,bar,mass,G1,G2(a);
CFunctions ga,pol,vrtx,prop2,p,prop,den,ga1,ga2,ga1b,ga2b,ga2five,hf,eps(a),eta,sym,asym,epssign;
Indices mu,nu,rho,photind,mu1,...,mu100,dum1,...,dum10,five;
Symbol d,d1,k,N,i,a1,...,a100,n1,n2,n3,n4,mb,mb2    ,s12,s13,s14,s23,s24,s34,convfac1proj,mark1,...,mark50,asbar,ab,au,aubar;
Vectors pp1,p1,...,p10,q1,q2,q3,q4,q,q14,q24,q34,q123,pu,pubar,ps,psbar,pb,pbbar;
Tensor O1,O,O1c,Obu,Osu,Obuc,Osuc,Ouu,Ouuc,Osb,Osbc;
unittrace d1;
Dimension d;
Off Statistics;


#include- all3vertxNEWvrtx.h;
#include- ProdTwoEps_eps_eta.h;
*#include- EpsScheme_eps_eta.h;
#include- etasimp.h
#include- tracesNoG5.h;
*#include epsBMscheme.h;
#include- AbsSquare.h;
#include- conjugate.h;

*
* split 4-vertex in 2 2-vertices and give them dirac structure
* create ga() as prototype to be converted to g_
*

* pinguin structure (sbar-b)(ubar-u)

id  vrtx(sbar(asbar?,psbar?),u(au?,pu?),ubar(aubar?,pubar?),b(ab?,pb?)) = vrtx(sbar(asbar,psbar),b(ab,pb))*vrtx(ubar(aubar,pubar),u(au,pu));

id  vrtx(ubar(aubar?,pubar?),u(au?,pu?)) = ga(aubar,Ouu,au);
id  vrtx(sbar(asbar?,psbar?),b(ab?,pb?)) = ga(asbar,Osb,ab);



id prop(f?(a1?,p1?))=prop2(f(a1,a1+1,p1));

*
* put spinors and propagators in ga-functions
* CHECK the sign vs. flow parts!!!
*
repeat;
id ga(?a1,O?,a2?)*prop2(s?(a3?,a2?,p1?))=mark13*ga(?a1,O,prop(s(p1)),a3);
id pol(photon(n1?,p1?))=p(li(n1),p1);
id pol(b?(n1?,p1?))*ga(n1?,?a2)=ga(b(p1),?a2);
id pol(b?(n1?,p1?))*ga(?a2,n1?)=ga(?a2,b(p1));
id ga(?a1,a2?)*prop2(u?(a2?,a3?,p1?))=ga(?a1,prop(u(p1)),a3);
id ga(a1?,?a2)*prop2(u?(a3?,a1?,p1?))=ga(a3,prop(u(p1)),?a2);

id ga(a1?,?a2)*prop2(u?(a1?,a3?,p1?))=mark10*ga(a3,prop(u(p1)),?a2); *(?SIGN?)

id ga(?a1,a2?)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),photon(a4?,p3?))=ga(?a1,li(photind),a3);
id ga(a1?,?a2)*vrtx(ubar?(a3?, p1?),u?(a1?,p2?),photon(a4?,p3?))=
ga(a3,li(photind),?a2);

id ga(a2?,?a1)*vrtx(ubar?(a2?, p1?),u?(a3?,p2?),photon(a4?,p3?))=
mark11*ga(a3,li(photind),?a1); *(?SIGN?)
id ga(?a1,a2?)*vrtx(ubar?(a3?, p1?),u?(a2?,p2?),photon(a4?,p3?))=
mark12*ga(?a1,li(photind),a3); *(?SIGN?)

endrepeat;

*
* assign number to the lines with b and u respectively
*
if (occurs(Osb)=1);
id,once ga(?a1)=ga1(?a1);
endif;
if (occurs(Ouu)=1);
id,once ga(?a1)=ga2(?a1);
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
*

.sort
#do j=1,4
#do i=1,4
Local D'j''i'tree = D'j'tree*D'i'treeC;
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
id ga1(s?(p2?),?a2,b?(p1?))*ga1b(bar(b?(p1?)),?a4,bar(s?(p2?)))=hf(b)*hf(s)*ga1(?a2,hel(b(p1)),?a4,hel(s(p2)));
id ga2(s?(p2?),?a2,b?(p1?))*ga2b(bar(b?(p1?)),?a4,bar(s?(p2?)))=hf(b)*hf(s)*ga2(?a2,hel(b(p1)),?a4,hel(s(p2)));
endrepeat;

*
* operators-bar = Oc
*

id ga1(?a1,bar(Ouu),?a2)=ga1(?a1,Ouuc,?a2);
id ga1(?a1,bar(Osb),?a2)=ga1(?a1,Osbc,?a2);
id ga2(?a1,bar(Ouu),?a2)=ga2(?a1,Ouuc,?a2);
id ga2(?a1,bar(Osb),?a2)=ga2(?a1,Osbc,?a2);

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


* make ga1,2 from CF to F to use chainout
.sort
Function ga1,ga2;

*
* convert ga to dirac chains
*
* put in mu*PL and PR*mu


chainout ga1;
id ga1(Osb) = 1/2*(ga1(mu)-ga1(mu,five));
id ga1(Osbc) = 1/2*(ga1(nu)+ga1(five,nu));
chainin ga1;

chainout ga2;
id ga2(Ouu) = ga2(mu);
id ga2(Ouuc) = ga2(nu);
chainin ga2;





.sort
#do j=1,4
#do i=1,4
Local D'j''i'treeLarin= D'j''i'tree;
*Local D'j''i'treeMisiak=D'j''i'tree;
#enddo
#enddo

.sort
#do j=1,4
#do i=1,4
Hide D'j''i'tree;
#enddo
#enddo


* operations on D44treeMisiak in "Misiak-scheme"
* anticommute 2 gamma five together
* cycle single gamma 5 to the end

.sort
#do j=1,4
#do i=1,4
Hide D'j''i'treeLarin;
#enddo
#enddo

id ga2(?a1,five,?a2,five,?a3)=(-1)**nargs_(?a2)*ga2(?a1,?a2,?a3);
id ga2(?a1,five,?a2)=ga2(?a2,?a1,five);

*
* antisymmetrize :
*

* for 8:
#do i=1,12
id ga1(mu1?,...,mu'i'?)=ga2(mu1,...,mu'i');
id ga2(mu1?,...,mu'i'?)=ga2(mu1,...,mu'i');
#enddo


id ga2(?mu1,five)=ga2five(?mu1);

id ga2five(?mu1)=sym(?mu1,five)+asym(?mu1,five)+distrib_(1,2,eta,ga2five,?mu1);

id ga2five(?mu1)=sym(?mu1,five)+asym(?mu1,five)+distrib_(1,2,eta,ga2five,?mu1);

id ga2five(?mu1)=sym(?mu1,five)+asym(?mu1,five)+distrib_(1,2,eta,ga2five,?mu1);


id asym(five)=0;
id asym(mu1?,...,mu2?,five)=0;
id asym(mu1?,...,mu4?,five)=-4*i*eps(mu1,...,mu4);
id asym(mu1?,...,mu6?,five)=0;
id asym(mu1?,...,mu8?,five)=0;
id sym(?a1)=0;

id ga2five(mu1?,mu2?)=0;
id ga2five=0;

#call TracesNoG5
#call etasimp


.sort
#do j=1,4
#do i=1,4
Hide D'j''i'treeMisiak;
#enddo
#enddo
.sort
#do j=1,4
#do i=1,4
*Unhide D'j''i'treeLarin;
Unhide D44treeLarin;
#enddo
#enddo


*
* LARIN SCHEME
*

* identities below make sure that terms like ga2(p3+p4) 
* are converted to ga2(p3)+ga2(p4)



* replace TR(...mu.five...) by i/6*eps(mu,m1,m2,m3)*TR(...m1.m2.m3...):

id ga2?(?mu1,mu2?,five,?mu3,mu4?,five,?mu5)=i/6*i/6*eps(mu2,dum1,dum2,dum3)*eps(mu4,dum4,dum5,dum6)*ga2(?mu1,dum1,dum2,dum3,?mu3,dum4,dum5,dum6,?mu5);


id ga2(?mu1,mu2?,five,?mu3)=-i/6*eps(mu2,dum1,dum2,dum3)*
ga2(?mu1,dum1,dum2,dum3,?mu3);

id ga2(mu1?,...,mu8?)=ga2(mu1,...,mu8);
id ga2(mu1?,...,mu10?)=ga2(mu1,...,mu10);
id ga2(mu1?,...,mu12?)=ga2(mu1,...,mu12);

*
* Plug in Trace-identities (from FeynCalc) and products of eps-tensors
*

#call TracesNoG5
#call etasimp


*#call EpsRepLarin;
#call EpsProd;


.sort
#do j=1,4
#do i=1,4
*Unhide D'j''i'treeMisiak;
#enddo
#enddo


id mark1=1;
id mark2=1;
id mark5=1;


id eta(p1?,p2?)=p1.p2;
id eps(p1,p2?,p3?,p4?)=eps(q1,p2,p3,p4)+eps(q2,p2,p3,p4)+
eps(q3,p2,p3,p4)+eps(q4,p2,p3,p4);

#call etasimp


id p1=(q1+q2+q3+q4);

id q1.q1=0;
id q2.q2=0;
id q3.q3=0;
id q4.q4=0;

id q1.q2=s12/2;
id q1.q3=s13/2;
id q1.q4=s14/2;
id q2.q3=s23/2;
id q2.q4=s24/2;
id q3.q4=s34/2;

id i^2=-1;
*id d=4;
id convfac1proj=1/2;

id p(?a1)=1;

id hf(u)=1;
id hf(ubar)=1;
id hf(s)=1;
id hf(b)=1/2;

id den(?a1)=1;
id mass(b)=mb;

id mb2=(s12+s13+s14+s23+s34+s24);

id epssign=1;

*id d1=4;

.sort 
#do j=1,4
#do i=1,4
*Local D'j''i'treeDiff = D'j''i'treeMisiak-D'j''i'treeLarin;
#enddo
#enddo


.sort
*save treediagscompare.sav;


Print;
.end


 
