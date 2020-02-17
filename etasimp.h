  #procedure Etasimp

* this procedure manages the contraction of the indices
* of eta(mu,nu)==g_mu_nu

repeat;
id eta(mu1?,mu2?)^2=d;
id eta(mu1?,mu1?)=d;
id eta(mu1?,mu2?)*eta(mu2?,mu1?)=d;
id eta(mu1?,mu2?)*eta(mu1?,mu3?)=eta(mu2,mu3);

id eta(mu1?,mu2?)*eps(mu1?,mu3?,mu4?,mu5?)=eps(mu2,mu3,mu4,mu5);
id eta(mu1?,mu2?)*eps(mu1?,mu2?,mu4?,mu5?)=0;
id eta(p1?,p2?)=p1.p2;
endrepeat;

#endprocedure
