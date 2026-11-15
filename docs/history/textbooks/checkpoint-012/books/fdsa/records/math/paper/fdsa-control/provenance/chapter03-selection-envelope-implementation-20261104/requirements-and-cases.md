# Selection envelope: requirements and independent cases

Root authors only two new files at held rounded candidate45d120ce. The existing
12 files and all related source/review records stay exact. This supports the
remaining actual C03-058 cost bridge without taking a supremum over payloads.
It does not itself close that row, prove a runtime, or change the book F.

For every natural d, define K_d=d*d+4*d+12 and B(n)=n*n+4*n+3.
Define U_d(0)=4 and U_d(n+1)=max(B(n+1),2*U_d(n)+K_d*(n+1)+7).
Prove U is monotone, dominates B and the invalid n+2 budget, and absorbs two
strictly smaller child budgets plus a toll at most K_d*n+7. A prefix bound is
U_d(max actualCutoff scalarCutoff), uniform in n and payloads. The eventual
algorithmic bridge must prove its actual toll and comparison; neither is an
assumption disguised as a result here. No finite or inhabited payload type is
introduced. d=0/1 remain harmless scalar cases; no termination claim for those
algorithm parameters follows.

Independent numerical expectations, calculated before source edits:
K_2=24, U_2(0)=4, U_2(1)=39, U_2(2)=133, U_2(3)=345.
K_5=57, U_5(0)=4, U_5(1)=72, U_5(2)=265, U_5(3)=708.
Small budgets at n0,1,2,3 are3,8,15,24.
At parent n2 and d2, children of sizes1 and0 admit budgets39 and4;
toll24*2+7=55; total98 is at most133. Connect this case to the general
strict-child transfer, not only numeric evaluation. Empty invalid budget2
is at most U_d(0)=4 for arbitrary d. A nonshrinking pair at d2,n1 has
total2*39+24+7=109, exceeding U_2(1)=39; strict decrease is necessary for
the stated transfer premise. For arbitrary d,a,b and n<=a or n<=b,
monotonicity yields U_d(n)<=U_d(max a b), with constants chosen before n.

The universal child-cost premises are local non-linear-budget comparisons,
not a desired linear-time assumption. They will be discharged by actual
well-founded execution induction. The envelope is intentionally coarse and
will only serve as a uniform finite base for the separately checked eventual
contracting recurrence. No new full check/type/audit/acceptance credit.
