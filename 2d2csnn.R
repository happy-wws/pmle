library(MASS)
library(mvtnorm)

r.msn <-
function(n, mu, var, theta)###generate the random samples from MSN distribution
{	
	d = length(mu)
	w = diag((diag(var))^0.5)
	var_bar = solve(w) %*% var %*% solve(w)
	delta = as.vector((1 + t(theta) %*% var_bar %*% theta)) ^ (-0.5) * var_bar %*% theta
	lambda = delta / (sqrt(1 - delta ^ 2))
	Ddelta = diag(as.vector(sqrt(1 - delta ^ 2)))
	Phi = solve(Ddelta) %*% var_bar %*% solve(Ddelta) - lambda %*% t(lambda)
	U0 = mvrnorm(n, rep(0, d), Phi)
	U1 = rnorm(n)
	x = Ddelta %*% t(U0) + delta %*% t(abs(U1))
	x = mu + w %*% x
	t(x)
}

rmix.msn <-
function (n, alpha, mu, var, theta)###generate the random samples from MSN mixture distribution 
#n:      sample size.
#alpha:  vector of mixture probabilities(m component).
#mu:   matrix of location parameter of each component(d*m).
#var:    matrix of scale matrix of each component(d*dm).
#theta:  matrix of slant parameter of each component(d*m).
{
	m = length(alpha)
	alpha = alpha/sum(alpha)
	data = c()
	nindex = rmultinom(1, n, alpha)
	d = nrow(mu)
	for(i in 1 : m)
		data = rbind(data, r.msn(nindex[i], as.vector(mu[, i]), var[, ((i - 1) * d + 1) : (i * d)], as.vector(theta[, i])))
	data
}

dmsn <-
function(x, mu, omega, theta)###density function of MSN distribution
{
	f = 2 * dmvnorm(x, mu, omega) * pnorm(t(theta) %*% diag(diag(omega) ^ (-0.5)) %*% (x - mu))
	as.numeric(f)
}

fln <-
function(x, alpha, mu, omega, theta, lambda, an, bn)###log-likelihood and penalized log-likelihood
{
	sn = var(x)
	an = an / n
	bn = bn / log(n)
	m = length(alpha)
	d = ncol(x)
	pdf.component = matrix(0, n, m)
	pn = 0
	for (j in 1 : m)
	{
		mu_j = mu[, j]
		omega_j = omega[, ((j - 1) * d + 1) : (j * d)]
		theta_j = theta[, j]
		for (i in 1 : n)
			pdf.component[i, j] =  dmsn(x[i, ], mu_j, omega_j, theta_j) * alpha[j]
		pn1 = - an * (sum(diag(sn %*% solve(omega_j))) + log(det(omega_j %*% solve(sn))))
		pn2 = - bn * (sum(theta_j ^ 2) - log(1 + sum(theta_j ^ 2)))
		pn = pn + pn1 + pn2 
	}
	pdf = apply(pdf.component, 1, sum)
	ln = sum(log(pdf))
	pln = ln + pn + lambda * sum(log(alpha))
	c(ln, pln)
}

iter.msn <- 
function(x, para0, lambda, an, bn)###iteration of EM algorithm
{
	n = nrow(x)
	d = ncol(x)
	sn = var(x)
	sigma = c()
	delta = c()
	eta = c()
	alpha = para0$alpha
	mu = para0$mu
	omega = para0$omega
	theta = para0$theta
	m = length(alpha)
	pdf.component = matrix(0, n, m)
	w = matrix(0, n, m)
	beta = matrix(0, n, m)
	gamma = matrix(0, n, m)
	###E-step of EM-algorithm
	for (j in 1 : m)
	{
		mu_j = mu[, j]
		omega_j = omega[, ((j - 1) * d + 1) : (j * d)]
		theta_j = theta[, j]
		var_barj = diag((diag(omega_j)) ^ (-0.5)) %*% omega_j %*% diag((diag(omega_j)) ^ (-0.5))
		delta_j = as.numeric((1 + t(theta_j) %*% var_barj %*% theta_j)) ^ (-0.5) * var_barj %*% theta_j
		eta_j = diag(diag(omega_j)) ^ 0.5 %*% delta_j
		sigma_j = omega_j - eta_j %*% t(eta_j)
		delta = cbind(delta, delta_j)
		eta = cbind(eta, eta_j)
		sigma = cbind(sigma, sigma_j)
		
		for (i in 1 : n)
		{	
			pdf.component[i, j] =  dmsn(x[i, ], mu_j, omega_j, theta_j) * alpha[j]
			mu_tau = t(x[i, ] - mu_j) %*% solve(sigma_j) %*% eta_j / (1 + t(eta_j) %*% solve(sigma_j) %*% eta_j)
			sigma_tau = 1 / (1 + t(eta_j) %*% solve(sigma_j) %*% eta_j)
			a = mu_tau / sigma_tau ^ 0.5
			if (pnorm(a) != 0)
				d_tau = dnorm(mu_tau / sigma_tau ^ 0.5) / pnorm(mu_tau / sigma_tau ^ 0.5)
			if (pnorm(a) == 0)
				d_tau = -a
			beta[i, j] = mu_tau + sigma_tau ^ 0.5 * d_tau
			gamma[i, j] = mu_tau ^ 2 + sigma_tau + mu_tau * sigma_tau ^ 0.5 * d_tau
		}
	}
	w = pdf.component / apply(pdf.component, 1, sum)
	###M-step of EM-algorithm
	an = an / n
	bn = bn / log(n)
	alpha = (apply(w, 2, sum) + lambda)/(n + m * lambda)
	for (j in 1 : m)
	{
		mu[, j] = (apply(w[, j] * x, 2, sum) - eta[, j] * sum(w[, j] * beta[, j])) / sum(w[, j])
		ff = function(par)
		{	
			l = length(par)
			omega_diag = par[1 : d]
			omega_upper = par[(d + 1) : (l - d)]
			theta = par[(l - d + 1) : l]
			omega = diag(omega_diag)
			omega[upper.tri(omega)] = omega_upper
			omega = t(omega) %*% omega
			var_bar = diag((diag(omega)) ^ (-0.5)) %*% omega %*% diag((diag(omega)) ^ (-0.5))
			delta = as.numeric((1 + t(theta) %*% var_bar %*% theta)) ^ (-0.5) * var_bar %*% theta
			eta = diag(diag(omega)) ^ 0.5 %*% delta
			sigma = omega - eta %*% t(eta)
			s = 0
			for (i in 1 : n)
			{	
				s0 = -log(det(sigma)) / 2
				s1 = -(t(x[i, ] - mu[, j])) %*% solve(sigma) %*% (x[i, ] - mu[, j]) / 2
				s2 = -(1 + t(eta) %*% solve(sigma) %*% eta) * gamma[i, j] / 2
				s3 = (t(x[i, ] - mu[, j])) %*% solve(sigma) %*% eta * beta[i, j]
				s = s + w[i, j] * (s0 + s1 + s2 + s3)
			}
			sp1 = - an * (sum(diag(sn %*% solve(omega))) + log(det(omega %*% solve(sn))))
			sp2 = - bn * (sum(theta ^ 2) - log(1 + sum(theta ^ 2)))
			ff = -(s0 + s + sp1 + sp2)
		}
		omega0 = chol(omega[, ((j - 1) * d + 1) : (j * d)])
		omega_diag = diag(omega0)
		omega_upper = omega0[upper.tri(omega0)]
		theta0 = theta[, j]
		par0 = c(omega_diag, omega_upper, theta0)
		if (is.na(ff(par0)) == F)
		{
			res = optim(par0, ff)
			res_par = res$par
			l = length(res_par)
			omega_diag = res_par[1 : d]
			omega_upper = res_par[(d + 1) : (l - d)]
			theta[, j] = res_par[(l - d + 1) : l]
			o = diag(omega_diag)
			o[upper.tri(o)] = omega_upper              
			omega[, ((j - 1) * d + 1) : (j * d)] = t(o) %*% o
		}
	}	
	###compute the log-likelihood and penalized log-likelihood value
	ln = fln(x, alpha, mu, omega, theta, lambda, an, bn)[1]
	pln = fln(x, alpha, mu, omega, theta, lambda, an, bn)[2]
	###output
	list('alpha' = alpha, 'mu' = mu, 'omega' = omega, 'theta' = theta, 'ln' = ln, 'pln' = pln)
}

phi.msn <-
function(x, m0, lambda, len, niter, tol, an, bn, pp)
{
#x: 		data, be a matrix with n rows and d columns.  
#m0:	 	order of finite normal mixture model.
#lambda:	size of penalized function of mixing distribution
#len:		number of initial values chosen for the EM-algorithm.	
#niter:     least number of iterations for all initial values in the EM-algorithm.
#tol:		tolerance value for the convergence of the EM-algorithm.
	n = nrow(x)
	d = ncol(x)
	sn = var(x)
	out_pln = c()
	out_alpha = c()
	out_mu = c()
	out_omega = c()
	out_theta = c()
	for (i in 1 : len)
	{
		print(i)
		if (i == 1)
			para0 = pp
		if (i > 1)
		###random initial values for EM-algorithm
		{
			alpha = runif(m0, 0, 1)
			alpha = alpha / sum(alpha)
			mu = c()
			theta = c()
			omega = c()
			for (j in 1 : d)
			{
				mu = rbind(mu, runif(m0, quantile(x[, j], 0.25), quantile(x[, j], 0.75)))
				#theta = rbind(theta, runif(m0, -5, 5))	
			}
			for (j in 1 : m0)
				omega = cbind(omega, sn * runif(1, 0.5, 2))
			para0 = list('alpha' = alpha, 'mu' = mu, 'omega' = omega, 'theta' = pp$theta)
		}
		for (j in 1 : niter)###run niter EM-iterations first
		{
			outpara = iter.msn(x, para0, lambda, an, bn)
			para0 = list('alpha' = outpara$alpha, 'mu' = outpara$mu, 'omega' = outpara$omega, 'theta' = outpara$theta)
			print(outpara$pln)
		}
		out_pln = c(out_pln, outpara$pln)
		out_alpha = rbind(out_alpha, outpara$alpha)
		out_mu = rbind(out_mu, outpara$mu)
		out_omega = rbind(out_omega, outpara$omega)
		out_theta = rbind(out_theta, outpara$theta)
	}
	index = which.max(out_pln)
	alpha0 = out_alpha[index, ]
	mu0 = out_mu[((index - 1) * d + 1) : (index * d), ]
	omega0 = out_omega[((index - 1) * d + 1) : (index * d), ]
	theta0 = out_theta[((index - 1) * d + 1) : (index * d), ]
	para0 = list('alpha' = alpha0, 'mu' = mu0, 'omega' = omega0, 'theta' = theta0)
	pln0 = out_pln[index]
	err = 1
	t = 0
	while (err > tol & t < 1000 & (is.na(pln0) == F))###EM-iteration with the initial value with the largest penalized log-likelihood
	{
		outpara = iter.msn(x, para0, lambda, an, bn)
		para0 = list('alpha' = outpara$alpha, 'mu' = outpara$mu, 'omega' = outpara$omega, 'theta' = outpara$theta)
		pln1 = outpara$pln
		err = pln1 - pln0
		pln0 = pln1
		t = t + 1
		print(t)
		print(pln1)
	}
	list('alpha' = outpara$alpha,
	'means' = outpara$mu,
	'variances' = outpara$omega,
	'skew' = outpara$theta,
	'loglik' = outpara$ln,
	'ploglik' = outpara$pln)
}

pmle.msn <-
function(x, m0 = 2, lambda = 0, len = 1, niter = 10, tol = 1e-3, an = 1, bn = 1, pp)
{
#x: 		data, be a matrix with n rows and d columns. 
#m0:	 	order of finite MSN mixture model.
#lambda:	size of penalized function of mixing distribution
#len:		number of initial values chosen for the EM-algorithm.	
#niter:      least number of iterations for all initial values in the EM-algorithm.
#tol:		tolerance value for the convergence of the EM-algorithm.

	out = phi.msn(x, m0, lambda, len, niter, tol, an, bn, pp)
	alphaa = out$alpha
	muu = out$means
	varr = out$variances
	thetaa = out$skew
	loglik = out$loglik
	ploglik = out$ploglik
	index = rank(alphaa)
	alpha = alphaa[index]
	mu = muu[, index]
	var = c()
	d = ncol(x)
	for (j in 1 : m0)
	{
		v = varr[, ((index[j] - 1) * d + 1) : (index[j] * d)]
		var = cbind(var, v)
	}
	theta = thetaa[, index]
	
	list('PMLE of mixing proportions' = alpha,
	'PMLE of location parameters' = mu, 
	'PMLE of scale matrices' = var,
	'PMLE of skew parameters' = theta,
	'log-likelihood' = loglik,
	'Penalized log-likelihood' = ploglik)
}

n1 = 100
n2 = 200
n3 = 500

alpha1 = c(0.3, 0.7)
alpha2 = c(0.4,0.6)
alpha3 = c(0.3,0.3,0.4)
alpha4 = c(0.2,0.3,0.2,0.3)


mu1 = c(-2, -2)
mu2 = c(0, 0)
mu3 = c(2, 2)
mu4 = c(4, 4)

Sigma1 = diag(c(1,1))
Sigma2 = diag(c(2,2))
Sigma3 = matrix(c(2,1,1,2),2,2)
Sigma4 = matrix(c(3,1,1,3),2,2)

shape1 =c(2,3)
shape2 =c(-2,-3)
shape3 =c(0,0)


n=n3
alpha = alpha2
mu = cbind(mu2, mu4)
var = cbind(Sigma2, Sigma4)
theta = cbind(shape1, shape3)
pp = list('alpha' = alpha, 'mu' = mu, 'omega' = var, 'theta' = theta)

ptm = proc.time()
talpha = c()
tmu = c()
tvar = c()
ttheta = c()
i = 0
while (i < 100)
{
	print(i)
	x = rmix.msn(n, alpha, mu, var, theta)
	res = pmle.msn(x, m0 = 2, pp = pp)
	if (is.na(res[[6]]) == F)
	{
		talpha = rbind(talpha, res[[1]])
		tmu = rbind(tmu, res[[2]])
		tvar = rbind(tvar, res[[3]])
		ttheta = rbind(ttheta, res[[4]])
		i = i + 1
	}
}
pptm = proc.time() - ptm

mu1 = tmu[seq(1, nrow(tmu), 2), ]###第一维度的均值
mu2 = tmu[seq(0, nrow(tmu), 2), ]###第二维度的均值
theta1 = ttheta[seq(1, nrow(ttheta), 2), ]###第一维度的偏度
theta2 = ttheta[seq(0, nrow(ttheta), 2), ]###第二维度的偏度
var1 = tvar[seq(1, nrow(tvar), 2), ]###协方差阵的第一行
var2 = tvar[seq(0, nrow(tvar), 2), ]###协方差阵的第二行
###第一成分结果
r1 = cbind(talpha[, 1], mu1[, 1], mu2[, 1], var1[, 1], var1[, 2], var2[, 2], theta1[, 1], theta2[, 1])
###第二成分结果
r2 = cbind(talpha[, 2], mu1[, 2], mu2[, 2], var1[, 3], var1[, 4], var2[, 4], theta1[, 2], theta2[, 2])

