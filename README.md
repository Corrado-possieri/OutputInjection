# OutputInjection
Macaulay2 Package to find an immersion that recast a nonlinear system into LIS form.

This package provides a set of functions to compute an immersion that recasts a 
nonlinear dynamical system into a linear one, up to an output injection. 
The functions included in this package are:
- "allEmbed" -- Compute all the embeddings of a system.
- "allEmbedtr" -- Compute all the truncated embeddings of a system.
- "approxSolODE" -- Approximate solution to an ODE.
- "compMatr" -- Companion matrix of a function with respect to an ideal.
- "immObs" -- Immersion into LIS form.
- "immObsNI" -- Immersion into LIS form without output transformation.
- "immObstr" -- Truncated immersion into LIS form.
- "immObstrNI" -- Truncated immersion into LIS form without transformation.
- "immObstrNum" -- Numerical immersion into LIS form with transformation.
- "obsForm" -- Observability form.
- "obsFormNI" -- Observability form without transformation.
- "rationalize" -- Rationalize a real number.
- "solveSystem" -- Solve a polynomial system of equalities.

In order to install Macaulay2, please follow the instructions given at
http://www.math.uiuc.edu/Macaulay2/Downloads/

Once that you have downloaded the file OutputInjectionPackage.m2,
the package can be loaded through the command 
load "LOCAL-PATH-TO-OutputInjectionPackage.m2";

In order to compute an immersion of the system

\dot{x}_1 = x_1-x_1^2+x_2,

\dot{x}_2 = x_1-x_1x_2,

y = x_1,

into LIS form, a minimal working example is

R = QQ[x_1,x_2];

f = matrix{{x_1-x_1^2+x_2},{x_1-x_1*x_2}};

h = x_1;

immObsNI(R,f,h,2,2)
