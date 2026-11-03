import Examples.ArithmeticPipeline
import Examples.MatrixStack
import Applications.Intervals.HigherOrder
import Applications.Languages.ConvolutionBridge

/-! Small executable displays; universal correctness proofs live in the imported modules. -/
namespace Examples.Run

def stackResult := ArithmeticPipeline.stackRun Arithmetic.shared [] ((), ((3 : ℚ), 2)) ()

def fourthPowerInterval :=
  (IntervalAnalysis.HigherOrder.compile IntervalAnalysis.HigherOrder.fourthPower).impl ()
    (⟨-1, 2⟩ : IntervalAnalysis.Interval)

def capturedCaseInterval :=
  (IntervalAnalysis.HigherOrder.compile IntervalAnalysis.HigherOrder.capturedCase).impl
    ((((), Sum.inl (⟨-1, 2⟩ : IntervalAnalysis.Interval)),
      IntervalAnalysis.HigherOrder.increment), ⟨10, 11⟩)

def recognizesProduct := LanguageDerivatives.recognize
  (LanguageDerivatives.compilePolynomial
    (Convolution.Polynomial.mul Convolution.Polynomial.sampleP Convolution.Polynomial.sampleQ))
  "abc".toList

#eval stackResult
#eval fourthPowerInterval
#eval capturedCaseInterval
#eval recognizesProduct

end Examples.Run
