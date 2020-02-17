#procedure Larin
*
* LARIN SCHEME
*
*
* replace TR(...mu.five...) by i/6*eps(mu,m1,m2,m3)*TR(...m1.m2.m3...):
*
* giving different names to the epsilons coming from different lines
* because the order of contraction later on matters
*

id ga1(?mu1,five,five,?mu3)=ga1(?mu1,?mu3);
id ga2(?mu1,five,five,?mu3)=ga2(?mu1,?mu3);

* twice

repeat;
id ga1(?mu1,mu2?,five,?mu3,mu4?,five,?mu5)=i/6*i/6*eps1(mu2,dum1,dum2,dum3)*eps1(mu4,dum4,dum5,dum6)*ga1(?mu1,dum1,dum2,dum3,?mu3,dum4,dum5,dum6,?mu5);
id ga2(?mu1,mu2?,five,?mu3,mu4?,five,?mu5)=i/6*i/6*eps2(mu2,dum7,dum8,dum9)*eps2(mu4,dum10,dum11,dum12)*ga2(?mu1,dum7,dum8,dum9,?mu3,dum10,dum11,dum12,?mu5);
endrepeat;

* once

id ga1(?mu1,mu2?,five,?mu3)=-a1*i/6*eps1(mu2,dum13,dum14,dum15)*ga1(?mu1,dum13,dum14,dum15,?mu3);
id ga2(?mu1,mu2?,five,?mu3)=-a1*i/6*eps2(mu2,dum16,dum17,dum18)*ga2(?mu1,dum16,dum17,dum18,?mu3);

*
* Checked value and speed of internal trace algorithm vs. external!
* values are the same: 50s vs 9200s in pinguin case
*

#endprocedure
