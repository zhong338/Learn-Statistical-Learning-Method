using Microsoft.VisualBasic.FileIO;
using System;
using System.Diagnostics;
using System.Runtime.Intrinsics.Arm;
using System.Runtime.Serialization;
using System.Security.Claims;
using System.Security.Cryptography;


namespace Assignment
{
    class option
    {
        //---------------------------------------------------------------------------------------------------------------------------------------------------------------

        // write the Gaussian CDF function using a numerical approximation
        public static double GaussianCDF(double x)
        {
            double k = 1.0 / (1.0 + 0.2316419 * Math.Abs(x));
            double kn = k;
            double sum = 0.0;

            for (int n = 1; n <= 5; ++n)
            {
                double coef = 0.0;
                switch (n)
                {
                    case 1:
                        coef = 0.319381530;
                        break;
                    case 2:
                        coef = -0.356563782;
                        break;
                    case 3:
                        coef = 1.781477937;
                        break;
                    case 4:
                        coef = -1.821255978;
                        break;
                    case 5:
                        coef = 1.330274429;
                        break;
                }

                sum += coef * kn;
                kn *= k;
            }

            double approx = 1.0 - 1.0 / Math.Sqrt(2 * Math.PI) * Math.Exp(-0.5 * x * x) * sum;
            return x >= 0.0 ? approx : 1.0 - approx;
        }

        public static double BlackScholesDelta(string optionType, double S0, double K, double sigma, double r, double T)
        {
            double d1 = (Math.Log(S0 / K) + (r + 0.5 * sigma * sigma) * T) / (sigma * Math.Sqrt(T));
            double deltaBase = GaussianCDF(d1);

            if (optionType.ToLower() == "call")
            {
                return deltaBase;
            }
            else if (optionType.ToLower() == "put")
            {
                return deltaBase - 1;
            }
            else
            {
                throw new ArgumentException("Invalid option type. Use 'call' or 'put'.");
            }
        }

        //---------------------------------------------------------------------------------------------------------------------------------------------------------------
        // Monte Carlo simulation with control variate
        public static (double option_value, double standard_error) MonteCarloPrice(string optionType, double S0, double K, double T, double r, double sigma, int M, int I, string anti, string CV, bool isMultithreaded)
        {
            double price = 0;
            double standard_error = 0;
            double dt = T / I;

            double nudt = (r - 0.5 * sigma * sigma) * dt;
            double sigmadt = sigma * Math.Sqrt(dt);
            double erddt = Math.Exp(r * dt);
            double beta1 = -1;

            double sum_ct = 0;
            double sum_ct_2 = 0;

            double sum_ct_A = 0;
            double sum_ct_2_A = 0;

            double[] option_value = new double[M];
            double[] option_value_anti = new double[M];
            double[,] stock_price = new double[M, I];
            double[,] stock_price_anti = new double[M, I];
            double[,] seq = new double[M, I];
            Random rand = new Random();

            if (isMultithreaded)
            {
                object lockObject = new object();
                ParallelOptions parallelOptions = new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount };
                Parallel.For(0, M, parallelOptions, i =>
                {
                    Random rand = new Random(i); // Seed differently for each thread

                    double St = S0;
                    double cv_0 = 0;

                    double St_1_A = S0;
                    double St_2_A = S0;
                    double cv_1_A = 0;
                    double cv_2_A = 0;

                    stock_price[i, 0] = S0;
                    stock_price_anti[i, 0] = S0;

                    for (int j = 1; j < I; j++)
                    {
                        double t = (j - 1) * dt;

                        double delta = BlackScholesDelta(optionType, St, K, sigma, r, T - t);
                        double epsilon = rand.NextDouble();
                        double z = Math.Sqrt(-2.0 * Math.Log(epsilon)) * Math.Cos(2.0 * Math.PI * rand.NextDouble());

                        double Stn = St * Math.Exp(nudt + sigmadt * z);
                        cv_0 = cv_0 + delta * (Stn - St * erddt);
                        St = Stn;

                        double t_A = (j - 1) * dt;
                        double delta1_A = BlackScholesDelta(optionType, St_1_A, K, sigma, r, T - t_A);
                        double delta2_A = BlackScholesDelta(optionType, St_2_A, K, sigma, r, T - t_A);

                        double Stn1_A = St_1_A * Math.Exp(nudt + sigmadt * z);
                        double Stn2_A = St_2_A * Math.Exp(nudt - sigmadt * z);
                        cv_1_A = cv_1_A + delta1_A * (Stn1_A - St_1_A * erddt);
                        cv_2_A = cv_2_A + delta2_A * (Stn2_A - St_2_A * erddt);
                        St_1_A = Stn1_A;
                        St_2_A = Stn2_A;

                        stock_price[i, j] = stock_price[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt + sigma * Math.Sqrt(dt) * seq[i, j]);
                        stock_price_anti[i, j] = stock_price_anti[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt - sigma * Math.Sqrt(dt) * seq[i, j]);
                    }

                    double CT;
                    double CT_A;
                    if (optionType == "call")
                    {
                        CT = Math.Max(0, St - K) + beta1 * cv_0;

                        CT_A = 0.5 * (Math.Max(0, St_1_A - K) + beta1 * cv_1_A + Math.Max(0, St_2_A - K) + beta1 * cv_2_A);
                    }
                    else
                    {
                        CT = Math.Max(0, K - St) + beta1 * cv_0;

                        CT_A = 0.5 * (Math.Max(0, K - St_2_A) + beta1 * cv_1_A + Math.Max(0, K - St_2_A) + beta1 * cv_2_A);
                    }

                    lock (lockObject)
                    {
                        sum_ct += CT;
                        sum_ct_2 += CT * CT;

                        sum_ct_A += CT_A;
                        sum_ct_2_A += CT_A * CT_A;
                    }


                });
            }
            else
            {
                // Single-threaded version
                Random singleThreadRand = new Random();


                for (int i = 0; i < M; i++)
                {
                    double St = S0;
                    double cv_0 = 0;

                    double St_1_A = S0;
                    double St_2_A = S0;
                    double cv_1_A = 0;
                    double cv_2_A = 0;

                    stock_price[i, 0] = S0;
                    stock_price_anti[i, 0] = S0;

                    for (int j = 1; j < I; j++)
                    {

                        double t = (j - 1) * dt;

                        double delta = BlackScholesDelta(optionType, St, K, sigma, r, T - t);
                        double epsilon = singleThreadRand.NextDouble();
                        double z = Math.Sqrt(-2.0 * Math.Log(epsilon)) * Math.Cos(2.0 * Math.PI * singleThreadRand.NextDouble());

                        double Stn = St * Math.Exp(nudt + sigmadt * z);
                        cv_0 = cv_0 + delta * (Stn - St * erddt);
                        St = Stn;


                           double t_A = (j - 1) * dt;
                           double delta1_A = BlackScholesDelta(optionType, St_1_A, K, sigma, r, T - t_A);
                           double delta2_A = BlackScholesDelta(optionType, St_2_A, K, sigma, r, T - t_A);



                           double Stn1_A = St_1_A * Math.Exp(nudt + sigmadt * z);
                           double Stn2_A = St_2_A * Math.Exp(nudt - sigmadt * z);
                           cv_1_A = cv_1_A + delta1_A * (Stn1_A - St_1_A * erddt);
                           cv_2_A = cv_2_A + delta2_A * (Stn2_A - St_2_A * erddt);
                           St_1_A = Stn1_A;
                           St_2_A = Stn2_A;

                           stock_price[i, j] = stock_price[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt + sigma * Math.Sqrt(dt) * seq[i, j]);
                           stock_price_anti[i, j] = stock_price_anti[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt - sigma * Math.Sqrt(dt) * seq[i, j]);
                    
                    }

                    double CT;
                    double CT_A;
                    if (optionType == "call")
                    {
                        CT = Math.Max(0, St - K) + beta1 * cv_0;

                        CT_A = 0.5 * (Math.Max(0, St_1_A - K) + beta1 * cv_1_A + Math.Max(0, St_2_A - K) + beta1 * cv_2_A);
                    }
                    else
                    {
                        CT = Math.Max(0, K - St) + beta1 * cv_0;

                        CT_A = 0.5 * (Math.Max(0, K - St_2_A) + beta1 * cv_1_A + Math.Max(0, K - St_2_A) + beta1 * cv_2_A);
                    }

                    sum_ct += CT;
                    sum_ct_2 += CT * CT;

                    sum_ct_A += CT_A;
                    sum_ct_2_A += CT_A * CT_A;
                }
            }
                // Post-processing and return
                if (CV == "yes")
                {
                    if (anti == "yes")
                    {
                        price = sum_ct_A / M * Math.Exp(-r * T);
                        standard_error = Math.Sqrt((sum_ct_2_A - sum_ct_A * sum_ct_A / M) * Math.Exp(-2 * r * T) / (M - 1)) / Math.Sqrt(M);
                    }
                    else
                    {
                        price = sum_ct / M * Math.Exp(-r * T);
                        standard_error = Math.Sqrt((sum_ct_2 - sum_ct * sum_ct / M) * Math.Exp(-2 * r * T) / (M - 1)) / Math.Sqrt(M);
                    }
                }

                else
                {
                    if (anti == "yes")
                    {
                        price = option_value_anti.Average();
                        standard_error = Math.Sqrt(option_value_anti.Select(x => Math.Pow(x - option_value_anti.Average(), 2)).Sum() / (M - 1)) / Math.Sqrt(M);
                    }
                    else
                    {
                        price = option_value.Average();
                        standard_error = Math.Sqrt(option_value.Select(x => Math.Pow(x - option_value.Average(), 2)).Sum() / (M - 1)) / Math.Sqrt(M);
                    }
                }


            
            return (price, standard_error);
            }

        public static (double option_value, double standard_error) MonteCarloAsianOptionPrice(string optionType, double S0, double K, double T, double r, double sigma, int M, int I, string anti, string CV, bool isMultithreaded)
        {
            double price = 0;
            double standard_error = 0;
            double dt = T / I;

            double nudt = (r - 0.5 * sigma * sigma) * dt;
            double sigmadt = sigma * Math.Sqrt(dt);
            double erddt = Math.Exp(r * dt);
            double beta1 = -1;

            double sum_ct = 0;
            double sum_ct_2 = 0;

            double sum_ct_A = 0;
            double sum_ct_2_A = 0;

            double[] option_value = new double[M];
            double[] option_value_anti = new double[M];
            double[,] stock_price = new double[M, I];
            double[,] stock_price_anti = new double[M, I];
            double[,] seq = new double[M, I];

            object lockObject = new object();

            if (isMultithreaded)
            {
                ParallelOptions parallelOptions = new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount };
                Parallel.For(0, M, parallelOptions, i =>
                {
                    Random rand = new Random(i); // Seed differently for each thread

                    double St = S0;
                    double cv_0 = 0;

                    double St_1_A = S0;
                    double St_2_A = S0;
                    double cv_1_A = 0;
                    double cv_2_A = 0;

                    stock_price[i, 0] = S0;
                    stock_price_anti[i, 0] = S0;

                    for (int j = 1; j < I; j++)
                    {
                        double t = (j - 1) * dt;

                        double delta = BlackScholesDelta(optionType, St, K, sigma, r, T - t);
                        double epsilon = rand.NextDouble();
                        double z = Math.Sqrt(-2.0 * Math.Log(epsilon)) * Math.Cos(2.0 * Math.PI * rand.NextDouble());

                        double Stn = St * Math.Exp(nudt + sigmadt * z);
                        cv_0 = cv_0 + delta * (Stn - St * erddt);
                        St = Stn;

                        double t_A = (j - 1) * dt;
                        double delta1_A = BlackScholesDelta(optionType, St_1_A, K, sigma, r, T - t_A);
                        double delta2_A = BlackScholesDelta(optionType, St_2_A, K, sigma, r, T - t_A);

                        double Stn1_A = St_1_A * Math.Exp(nudt + sigmadt * z);
                        double Stn2_A = St_2_A * Math.Exp(nudt - sigmadt * z);
                        cv_1_A = cv_1_A + delta1_A * (Stn1_A - St_1_A * erddt);
                        cv_2_A = cv_2_A + delta2_A * (Stn2_A - St_2_A * erddt);
                        St_1_A = Stn1_A;
                        St_2_A = Stn2_A;

                        stock_price[i, j] = stock_price[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt + sigma * Math.Sqrt(dt) * seq[i, j]);
                        stock_price_anti[i, j] = stock_price_anti[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt - sigma * Math.Sqrt(dt) * seq[i, j]);
                    }

                    double CT;
                    double CT_A;
                    if (optionType == "call")
                    {
                        CT = Math.Max(0, St - K) + beta1 * cv_0;
                        CT_A = 0.5 * (Math.Max(0, St_1_A - K) + beta1 * cv_1_A + Math.Max(0, St_2_A - K) + beta1 * cv_2_A);
                    }
                    else
                    {
                        CT = Math.Max(0, K - St) + beta1 * cv_0;
                        CT_A = 0.5 * (Math.Max(0, K - St_2_A) + beta1 * cv_1_A + Math.Max(0, K - St_2_A) + beta1 * cv_2_A);
                    }

                    lock (lockObject)
                    {
                        sum_ct += CT;
                        sum_ct_2 += CT * CT;
                        sum_ct_A += CT_A;
                        sum_ct_2_A += CT_A * CT_A;
                    }
                });
            }
            else
            {
                // Single-threaded version
                Random singleThreadRand = new Random();

                for (int i = 0; i < M; i++)
                {
                    double St = S0;
                    double cv_0 = 0;

                    double St_1_A = S0;
                    double St_2_A = S0;
                    double cv_1_A = 0;
                    double cv_2_A = 0;

                    stock_price[i, 0] = S0;
                    stock_price_anti[i, 0] = S0;

                    for (int j = 1; j < I; j++)
                    {
                        double t = (j - 1) * dt;

                        double delta = BlackScholesDelta(optionType, St, K, sigma, r, T - t);
                        double epsilon = singleThreadRand.NextDouble();
                        double z = Math.Sqrt(-2.0 * Math.Log(epsilon)) * Math.Cos(2.0 * Math.PI * singleThreadRand.NextDouble());

                        double Stn = St * Math.Exp(nudt + sigmadt * z);
                        cv_0 = cv_0 + delta * (Stn - St * erddt);
                        St = Stn;

                        double t_A = (j - 1) * dt;
                        double delta1_A = BlackScholesDelta(optionType, St_1_A, K, sigma, r, T - t_A);
                        double delta2_A = BlackScholesDelta(optionType, St_2_A, K, sigma, r, T - t_A);

                        double Stn1_A = St_1_A * Math.Exp(nudt + sigmadt * z);
                        double Stn2_A = St_2_A * Math.Exp(nudt - sigmadt * z);
                        cv_1_A = cv_1_A + delta1_A * (Stn1_A - St_1_A * erddt);
                        cv_2_A = cv_2_A + delta2_A * (Stn2_A - St_2_A * erddt);
                        St_1_A = Stn1_A;
                        St_2_A = Stn2_A;

                        stock_price[i, j] = stock_price[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt + sigma * Math.Sqrt(dt) * seq[i, j]);
                        stock_price_anti[i, j] = stock_price_anti[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt - sigma * Math.Sqrt(dt) * seq[i, j]);
                    }

                    double CT;
                    double CT_A;
                    if (optionType == "call")
                    {
                        CT = Math.Max(0, St - K) + beta1 * cv_0;
                        CT_A = 0.5 * (Math.Max(0, St_1_A - K) + beta1 * cv_1_A + Math.Max(0, St_2_A - K) + beta1 * cv_2_A);
                    }
                    else
                    {
                        CT = Math.Max(0, K - St) + beta1 * cv_0;
                        CT_A = 0.5 * (Math.Max(0, K - St_2_A) + beta1 * cv_1_A + Math.Max(0, K - St_2_A) + beta1 * cv_2_A);
                    }

                    lock (lockObject)
                    {
                        sum_ct += CT;
                        sum_ct_2 += CT * CT;
                        sum_ct_A += CT_A;
                        sum_ct_2_A += CT_A * CT_A;
                    }
                }
            }

            // Post-processing and return
            if (CV == "yes")
            {
                if (anti == "yes")
                {
                    price = sum_ct_A / M * Math.Exp(-r * T);
                    standard_error = Math.Sqrt((sum_ct_2_A - sum_ct_A * sum_ct_A / M) * Math.Exp(-2 * r * T) / (M - 1)) / Math.Sqrt(M);
                }
                else
                {
                    price = sum_ct / M * Math.Exp(-r * T);
                    standard_error = Math.Sqrt((sum_ct_2 - sum_ct * sum_ct / M) * Math.Exp(-2 * r * T) / (M - 1)) / Math.Sqrt(M);
                }
            }
            else
            {
                if (anti == "yes")
                {
                    price = option_value_anti.Average();
                    standard_error = Math.Sqrt(option_value_anti.Select(x => Math.Pow(x - option_value_anti.Average(), 2)).Sum() / (M - 1)) / Math.Sqrt(M);
                }
                else
                {
                    price = option_value.Average();
                    standard_error = Math.Sqrt(option_value.Select(x => Math.Pow(x - option_value.Average(), 2)).Sum() / (M - 1)) / Math.Sqrt(M);
                }
            }

            return (price, standard_error);
        }

        public static (double option_value, double standard_error) MonteCarloDigitalOptionPrice(string optionType, double S0, double K, double T, double r, double sigma, int I, string anti, string CV, bool isMultithreaded, double payoutAmount)
        {
            double price = 0;
            double standard_error = 0;
            double dt = T / I;

            double nudt = (r - 0.5 * sigma * sigma) * dt;
            double sigmadt = sigma * Math.Sqrt(dt);
            double erddt = Math.Exp(r * dt);
            double beta1 = -1;

            double sum_ct = 0;
            double sum_ct_2 = 0;

            double sum_ct_A = 0;
            double sum_ct_2_A = 0;

            double[] option_value = new double[M];
            double[] option_value_anti = new double[M];
            double[,] stock_price = new double[M, I];
            double[,] stock_price_anti = new double[M, I];
            double[,] seq = new double[M, I];
            Random rand = new Random();

            if (isMultithreaded)
            {
                object lockObject = new object();
                ParallelOptions parallelOptions = new ParallelOptions { MaxDegreeOfParallelism = Environment.ProcessorCount };
                Parallel.For(0, M, parallelOptions, i =>
                {
                    Random rand = new Random(i); // Seed differently for each thread

                    double St = S0;
                    double cv_0 = 0;

                    double St_1_A = S0;
                    double St_2_A = S0;
                    double cv_1_A = 0;
                    double cv_2_A = 0;

                    stock_price[i, 0] = S0;
                    stock_price_anti[i, 0] = S0;

                    for (int j = 1; j < I; j++)
                    {
                        double t = (j - 1) * dt;

                        double delta = BlackScholesDelta(optionType, St, K, sigma, r, T - t);
                        double epsilon = rand.NextDouble();
                        double z = Math.Sqrt(-2.0 * Math.Log(epsilon)) * Math.Cos(2.0 * Math.PI * rand.NextDouble());

                        double Stn = St * Math.Exp(nudt + sigmadt * z);
                        cv_0 = cv_0 + delta * (Stn - St * erddt);
                        St = Stn;

                        
                        double t_A = (j - 1) * dt;
                        double delta1_A = BlackScholesDelta(optionType, St_1_A, K, sigma, r, T - t_A);
                        double delta2_A = BlackScholesDelta(optionType, St_2_A, K, sigma, r, T - t_A);

                        double Stn1_A = St_1_A * Math.Exp(nudt + sigmadt * z);
                        double Stn2_A = St_2_A * Math.Exp(nudt - sigmadt * z);
                        cv_1_A = cv_1_A + delta1_A * (Stn1_A - St_1_A * erddt);
                        cv_2_A = cv_2_A + delta2_A * (Stn2_A - St_2_A * erddt);
                        St_1_A = Stn1_A;
                        St_2_A = Stn2_A;

                        stock_price[i, j] = stock_price[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt + sigma * Math.Sqrt(dt) * seq[i, j]);
                        stock_price_anti[i, j] = stock_price_anti[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt - sigma * Math.Sqrt(dt) * seq[i, j]);
                    }

                    double CT;
                    double CT_A;
                    if (optionType == "call")
                    {
                        CT = St >= K ? payoutAmount : 0;
                        // CT = Math.Max(0, St - K) + beta1 * cv_0;
                        // CT_A = 0.5 * (Math.Max(0, St_1_A - K) + beta1 * cv_1_A + Math.Max(0, St_2_A - K) + beta1 * cv_2_A);
                        CT_A = 0.5 * ((St_1_A >= K ? payoutAmount : 0) + (St_2_A >= K ? payoutAmount : 0));
                    }
                    else
                    {
                        // CT = Math.Max(0, K - St) + beta1 * cv_0;
                        CT = St <= K ? payoutAmount : 0;
                        CT_A = 0.5 * ((K - St_2_A >= K ? payoutAmount : 0) + (K - St_2_A >= K ? payoutAmount : 0));

                        // CT_A = 0.5 * (Math.Max(0, K - St_2_A) + beta1 * cv_1_A + Math.Max(0, K - St_2_A) + beta1 * cv_2_A);
                    }

                    lock (lockObject)
                    {
                        sum_ct += CT;
                        sum_ct_2 += CT * CT;

                        sum_ct_A += CT_A;
                        sum_ct_2_A += CT_A * CT_A;
                    }


                });
            }
            else
            {
                // Single-threaded version
                Random singleThreadRand = new Random();


                for (int i = 0; i < I; i++)
                {
                    double St = S0;
                    double cv_0 = 0;

                    double St_1_A = S0;
                    double St_2_A = S0;
                    double cv_1_A = 0;
                    double cv_2_A = 0;

                    stock_price[i, 0] = S0;
                    stock_price_anti[i, 0] = S0;

                    for (int j = 1; j < I; j++)
                    {

                        double t = (j - 1) * dt;

                        double delta = BlackScholesDelta(optionType, St, K, sigma, r, T - t);
                        double epsilon = singleThreadRand.NextDouble();
                        double z = Math.Sqrt(-2.0 * Math.Log(epsilon)) * Math.Cos(2.0 * Math.PI * singleThreadRand.NextDouble());

                        double Stn = St * Math.Exp(nudt + sigmadt * z);
                        cv_0 = cv_0 + delta * (Stn - St * erddt);
                        St = Stn;


                        double t_A = (j - 1) * dt;
                        double delta1_A = BlackScholesDelta(optionType, St_1_A, K, sigma, r, T - t_A);
                        double delta2_A = BlackScholesDelta(optionType, St_2_A, K, sigma, r, T - t_A);



                        double Stn1_A = St_1_A * Math.Exp(nudt + sigmadt * z);
                        double Stn2_A = St_2_A * Math.Exp(nudt - sigmadt * z);
                        cv_1_A = cv_1_A + delta1_A * (Stn1_A - St_1_A * erddt);
                        cv_2_A = cv_2_A + delta2_A * (Stn2_A - St_2_A * erddt);
                        St_1_A = Stn1_A;
                        St_2_A = Stn2_A;

                        stock_price[i, j] = stock_price[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt + sigma * Math.Sqrt(dt) * seq[i, j]);
                        stock_price_anti[i, j] = stock_price_anti[i, j - 1] * Math.Exp((r - 0.5 * sigma * sigma) * dt - sigma * Math.Sqrt(dt) * seq[i, j]);

                    }

                    double CT;
                    double CT_A;
                    if (optionType == "call")
                    {
                        // CT = Math.Max(0, St - K) + beta1 * cv_0;
                        CT = St >= K ? payoutAmount : 0;

                        // CT_A = 0.5 * (Math.Max(0, St_1_A - K) + beta1 * cv_1_A + Math.Max(0, St_2_A - K) + beta1 * cv_2_A);
                        CT_A = 0.5 * ((St_1_A >= K ? payoutAmount : 0) + (St_2_A >= K ? payoutAmount : 0));
                    }
                    else
                    {
                        // CT = Math.Max(0, K - St) + beta1 * cv_0;
                        CT = St <= K ? payoutAmount : 0;

                        // CT_A = 0.5 * (Math.Max(0, K - St_2_A) + beta1 * cv_1_A + Math.Max(0, K - St_2_A) + beta1 * cv_2_A);
                        CT_A = 0.5 * ((K - St_2_A >= K ? payoutAmount : 0) + (K - St_2_A >= K ? payoutAmount : 0));
                    }

                    sum_ct += CT;
                    sum_ct_2 += CT * CT;

                    sum_ct_A += CT_A;
                    sum_ct_2_A += CT_A * CT_A;
                }
            }
            // Post-processing and return
            if (CV == "yes")
            {
                if (anti == "yes")
                {
                    price = sum_ct_A / I * Math.Exp(-r * T);
                    standard_error = Math.Sqrt((sum_ct_2_A - sum_ct_A * sum_ct_A / I) * Math.Exp(-2 * r * T) / (I - 1));
                }
                else
                {
                    price = sum_ct / I * Math.Exp(-r * T);
                    standard_error = Math.Sqrt((sum_ct_2 - sum_ct * sum_ct / I) * Math.Exp(-2 * r * T) / (I - 1));
                }
            }

            else
            {
                if (anti == "yes")
                {
                    price = option_value_anti.Average();
                    standard_error = Math.Sqrt(option_value_anti.Select(x => Math.Pow(x - option_value_anti.Average(), 2)).Sum() / (I - 1));
                }
                else
                {
                    price = option_value.Average();
                    standard_error = Math.Sqrt(option_value.Select(x => Math.Pow(x - option_value.Average(), 2)).Sum() / (I - 1));
                }
            }



            return (price, standard_error);
        }

        public static (double delta, double gamma, double vega, double theta, double rho) greeks(double S0, double K, double T, double r, double sigma, int M, int I, string optionType, string anti, string cv, bool isMultithreaded, bool isAsianGreeks)
            {
                double delta, delta1, delta2, gamma, vega, theta, rho;
                double delta_A, gamma_A, vega_A, theta_A, rho_A;

                // Calculate Delta
                delta = (MonteCarloPrice(optionType, S0 * 1.05, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloPrice(optionType, S0 * 0.95, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (2 * S0 * 0.05);
                

                // Calculate Gamma
                delta1 = (MonteCarloPrice(optionType, S0 * 1.05, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloPrice(optionType, S0, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (S0 * 0.05);
                delta2 = (MonteCarloPrice(optionType, S0, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloPrice(optionType, S0 * 0.95, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (S0 * 0.05);
                gamma = 2 * (delta1 - delta2) / (2 * S0 * 0.05);
                
                // Calculate Vega
                vega = (MonteCarloPrice(optionType, S0, K, r, sigma * 1.05, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloPrice(optionType, S0, K, r, sigma * 0.95, T, M, I, anti, cv, isMultithreaded).option_value) / (0.1 * sigma);
                

                // Calculate Theta
                theta = (MonteCarloPrice(optionType, S0, K, r, sigma, T * 0.95, M, I, anti, cv, isMultithreaded).option_value - MonteCarloPrice(optionType, S0, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (T * 0.05);
                
                // Calculate Rho
                rho = (MonteCarloPrice(optionType, S0, K, r * 1.05, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloPrice(optionType, S0, K, r * 0.95, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (0.1 * r);
                
                
                if (isAsianGreeks)
                {
                delta_A = (MonteCarloAsianOptionPrice(optionType, S0 * 1.05, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloAsianOptionPrice(optionType, S0 * 0.95, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (2 * S0 * 0.05);
                gamma_A = (MonteCarloAsianOptionPrice(optionType, S0 * 1.05, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloAsianOptionPrice(optionType, S0, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (S0 * 0.05);
                vega_A = (MonteCarloAsianOptionPrice(optionType, S0, K, r, sigma * 1.05, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloAsianOptionPrice(optionType, S0, K, r, sigma * 0.95, T, M, I, anti, cv, isMultithreaded).option_value) / (0.1 * sigma);
                theta_A = (MonteCarloAsianOptionPrice(optionType, S0, K, r, sigma, T * 0.95, M, I, anti, cv, isMultithreaded).option_value - MonteCarloAsianOptionPrice(optionType, S0, K, r, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (T * 0.05);
                rho_A = (MonteCarloAsianOptionPrice(optionType, S0, K, r * 1.05, sigma, T, M, I, anti, cv, isMultithreaded).option_value - MonteCarloAsianOptionPrice(optionType, S0, K, r * 0.95, sigma, T, M, I, anti, cv, isMultithreaded).option_value) / (0.1 * r);
                return (delta_A, gamma_A, vega_A, theta_A, rho_A);
                }
                else
                {
                return (delta, gamma, vega, theta, rho);
                }

        }

    }



        //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
        public class Sequence
        {
            // Van der Corput sequence 
            static double[] VanDerCorput(int b, int n)
            {
                double[] sequence = new double[n];

                for (int i = 1; i <= n; i++)
                {
                    int d = i;
                    double x = 0.0;
                    double f = 1.0 / b;

                    while (d > 0)
                    {
                        x += (d % b) * f;
                        d /= b;
                        f /= b;
                    }

                    sequence[i - 1] = x;
                }

                return sequence;
            }
            //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

            public class MainFunction
            {
                static void Main(string[] args)
                {
                    // Variables
                    string optionType;
                    string anti;
                    string cv;
                    double S0, K, r, sigma, T;
                    int M, I;
                    double option_value = 0;
                    double standard_error = 0;
                    double delta, gamma, vega, theta, rho;

                //++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
                    // User input
                    Console.WriteLine("Welcome to the Monte Carlo Option Pricing Calculator!");
                    Console.WriteLine("Select the option type: (1) European, (2) Asian, (3) Barrier, (4) Lookback, (5) Digital, (6) Range");
                    int optionTypeResponse = Convert.ToInt32(Console.ReadLine());
                    
                    switch (optionTypeResponse)
                    {
                        case 1:
                            optionType = "European";
                            break;
                        case 2:
                            optionType = "asian";
                            break;
                        case 3:
                            optionType = "barrier";
                            break;
                        case 4:
                            optionType = "lookback";
                            break;
                        case 5:
                            optionType = "digital";
                            break;
                        case 6:
                            optionType = "range";
                            break;
                        default:
                            optionType = "European";
                            break;
                    }

                    Console.WriteLine("Please enter the parameters in the following format: S0,K,r,sigma,T,M,I,call or put");

                    string input = Console.ReadLine();
                    if (string.IsNullOrEmpty(input))
                    {
                        Console.WriteLine("Invalid input, exiting.");
                        return;
                    }

                    string[] parameters = input.Split(new[] { ',', ' ' }, StringSplitOptions.RemoveEmptyEntries);

                    if (parameters.Length != 8)
                    {
                        Console.WriteLine("Incorrect number of parameters, exiting.");
                        return;
                    }

                    try
                    {
                        S0 = Convert.ToDouble(parameters[0]);
                        K = Convert.ToDouble(parameters[1]);
                        r = Convert.ToDouble(parameters[2]);
                        sigma = Convert.ToDouble(parameters[3]);
                        T = Convert.ToDouble(parameters[4]);
                        M = Convert.ToInt32(parameters[5]);
                        I = Convert.ToInt32(parameters[6]);
                        optionType = parameters[7].ToLower();

                        Console.WriteLine("Do you want to apply antithetic variance? (yes or no)");
                        anti = Console.ReadLine()!;
                        Console.WriteLine("");

                        Console.WriteLine("Do you want to apply control variate? (yes or no)");
                        cv = Console.ReadLine()!;
                        Console.WriteLine("");

                        Console.WriteLine("Do you want to apply multithreading? (yes or no)");
                        string multithreadingResponse = Console.ReadLine().ToLower();
                        bool isMultithreaded = (multithreadingResponse == "yes");
                        Console.WriteLine("");

                        

                        if (optionTypeResponse == 1)

                    {
                        bool isAsianGreeks = false;
                        (option_value, standard_error) = option.MonteCarloPrice(optionType, S0, K, T, r, sigma, M, I, anti, cv, isMultithreaded);
                        (delta, gamma, vega, theta, rho) = option.greeks(S0, K, T, r, sigma, M, I, optionType, anti, cv, isMultithreaded,isAsianGreeks);
                        Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                        Console.WriteLine("");
                        Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}.");
                        }
                        else if (optionTypeResponse == 2)
                    {   
                        bool isAsianGreeks = true;
                        (option_value, standard_error) = option.MonteCarloAsianOptionPrice(optionType, S0, K, T, r, sigma, M, I, anti, cv, isMultithreaded);
                        (delta, gamma, vega, theta, rho) = option.greeks(S0, K, T, r, sigma, M, I, optionType, anti, cv, isMultithreaded, isAsianGreeks);
                            Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                            Console.WriteLine("");
                            Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}.");
                        }
                        /*
                        else if (optionTypeResponse == 3)
                    {
                            Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                            Console.WriteLine("");
                            Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}.");
                        }
                        else if (optionTypeResponse == 4)
                    {
                            Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                            Console.WriteLine("");
                            Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}.");
                        }
                        else if (optionTypeResponse == 5)
                    {
                            Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                            Console.WriteLine("");
                            Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}.");
                        }
                        else if (optionTypeResponse == 6)
                    {
                            Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                            Console.WriteLine("");
                            Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}.");
                        }*/
                        else
                    {
                            Console.WriteLine("Invalid option type, exiting.");
                            return;
                        }
                        /* 
                        Console.WriteLine($"The option value is {option_value} with a standard error of {standard_error}.");
                        Console.WriteLine("");
                        Console.WriteLine($"The Greeks (delta, gamma, vega, theta, rho) are {delta}, {gamma}, {vega}, {theta}, {rho}."); */

                }
                    catch (Exception e)
                    {
                    Console.WriteLine($"An error occurred: {e.Message}");
                    return;
                    }
                }
            }
        }
}