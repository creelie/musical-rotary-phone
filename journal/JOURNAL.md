# Target journal: The Fibonacci Quarterly

| Item | Details |
|---|---|
| Journal | The Fibonacci Quarterly (journal of the Fibonacci Association) |
| Publisher | Taylor & Francis (Informa UK), since 2025 |
| ISSN | 0015-0517 (print), 2641-340X (electronic), both from the Crossref journal record |
| Homepage | https://www.tandfonline.com/journals/ufbq20 |
| Fibonacci Association page | https://www.fibonacciassociation.org/fibonacciquarterly (editorial board; Editor-in-Chief Anitha Srinivasan) |
| Submission | "Submit an article" on the Taylor & Francis homepage above, which leads to the Taylor & Francis submission system |
| Contact | FibonacciAssociation@gmail.com |
| Template | The journal's LaTeX template (`FQtemplate25g1.tex` with the Taylor & Francis `interact` class), from https://www.fibonacciassociation.org/helpful-files; `paper/interact.cls` is the class file shipped with it |

## Scope fit

The journal publishes research on Fibonacci numbers, Lucas numbers and related
integer sequences. The paper is about representations of integers by the
Fibonacci and Lucas numbers and settles three conjectures recorded in the
OEIS. The closest prior work appeared in the same journal:

- L. Carlitz, R. Scoville, V. E. Hoggatt, Jr., Lucas representations,
  Fibonacci Quart. 10(1) (1972) 29-42, doi:10.1080/00150517.1972.12430968.
- J. Pihko, On Fibonacci and Lucas representations and a theorem of
  Lekkerkerker, Fibonacci Quart. 26(3) (1988) 256-261,
  doi:10.1080/00150517.1988.12429631.
- M. Kologlu, G. S. Kopp, S. J. Miller, Y. Wang, On the number of summands in
  Zeckendorf decompositions, Fibonacci Quart. 49(2) (2011) 116-130,
  doi:10.1080/00150517.2011.12428056.

The conjectures proved:

- Kimberling (A214981; J. Integer Seq. 23 (2020), Article 20.9.5, Section 6):
  the limit of A179180(n)/A214981(n) exists and lies in (1.2, 1.4). The limit
  is (5 - sqrt 5)/2.
- Greathouse (A214973, 2021): A049651(n) is the first occurrence of n in
  A214973.
- Kurkov (A214973, 2021): A214973(n) = A329320(A048679(n)) for n > 0.

The Journal of Integer Sequences, where Kimberling stated the first
conjecture, was not chosen: its submission instructions forbid text written
by a large language model.

## Length and format

- The manuscript is 9 pages in the journal template, by Deep Bhattacharjee
  (corresponding author) and Ushashi Bhattacharya, with a two-sentence
  abstract, keywords separated by semicolons, three figures, and MSC2020
  codes (Primary 11B39; Secondary 11A67, 68V15) after the references.
- The source is a single file `main.tex` with the class file `interact.cls`
  and the three figures as PNG in `figures/`; the references are in the source
  (`thebibliography`), so no `.bib` or `.bbl` file is needed.
  `dist/KimberlingConjecture_final2-tex.zip` and the arXiv tarball contain
  exactly these files.
- The paper names no program or file; the computations and the Lean
  formalization are described in prose, and the archive is cited under Data
  availability.
- Template rules followed: references in alphabetical order, numbered, in the
  Taylor & Francis MAA style, with DOIs; every OEIS sequence cited by its
  A-number; no contractions or abbreviations such as "iff" or "e.g."; periods
  at the end of sentences that end with a displayed equation; a centered dot
  only between two numbers; proofs end with the open square; a "Disclosure
  statement" section (competing interests: none) and a "Funding" section
  (none) before the references; AI use acknowledged in the "Acknowledgements"
  section; a "Data availability" section with the Zenodo DOI of the Lean
  formalization and the link to the PDF in `preprintKimberlingConjecture/`.
- The template's month, year, volume and number fields are left as
  placeholders for the production office.
- The journal's instructions for authors on tandfonline.com returned HTTP 403
  to the session that prepared this file, so any page limit or other
  journal-specific requirement there was not read; check it before submitting.

## Policy on AI assistance

- Template (Acknowledgements section): "If AI technology has been used in the
  creation of this article, including for translation purposes, then it
  should be acknowledged in this section." The paper does this.
- Taylor & Francis AI policy
  (https://taylorandfrancis.com/our-policies/ai-policy/, read for this file):
  generative AI tools must not be listed as authors; authors must acknowledge
  any use of generative AI tools in the article through a statement that
  gives the full name of the tool (with version number), how it was used and
  the reason for use; authors remain accountable for the originality,
  validity and integrity of the content, including the references, and must
  review all AI output. Text or code generation without rigorous revision is
  not acceptable.
- The statement in `paper/main.tex` names Claude Code (Anthropic), how it was
  used and why. Add the version number of the tool in the submitted
  manuscript, as the policy asks.
- Every statement of Theorems 1.4 to 1.6 is checked by the Lean 4 kernel
  (Section 6 of the paper), and
  every DOI in the bibliography was checked against its Crossref record.
