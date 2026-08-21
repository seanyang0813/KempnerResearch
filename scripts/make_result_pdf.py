#!/usr/bin/env python3
"""Build the self-contained Kempner coprime-fiber research note PDF."""

from __future__ import annotations

from pathlib import Path

from reportlab.lib import colors
from reportlab.lib.enums import TA_CENTER, TA_LEFT
from reportlab.lib.pagesizes import A4
from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
from reportlab.lib.units import inch, mm
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.platypus import (
    BaseDocTemplate,
    Frame,
    HRFlowable,
    KeepTogether,
    PageBreak,
    PageTemplate,
    Paragraph,
    Spacer,
    Table,
    TableStyle,
)


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "output" / "pdf" / "kempner_coprime_fiber_result.pdf"

NAVY = colors.HexColor("#17324D")
BLUE = colors.HexColor("#246B8E")
TEAL = colors.HexColor("#177E89")
PALE_TEAL = colors.HexColor("#EAF6F7")
PALE_BLUE = colors.HexColor("#EEF4F8")
PALE_AMBER = colors.HexColor("#FFF5DB")
AMBER = colors.HexColor("#A96800")
INK = colors.HexColor("#1D2730")
MUTED = colors.HexColor("#536471")
RULE = colors.HexColor("#CAD6DE")
WHITE = colors.white


def register_fonts() -> None:
    font_dir = Path("/usr/share/fonts/truetype/dejavu")
    pdfmetrics.registerFont(TTFont("DV", str(font_dir / "DejaVuSans.ttf")))
    pdfmetrics.registerFont(TTFont("DV-Bold", str(font_dir / "DejaVuSans-Bold.ttf")))
    pdfmetrics.registerFont(TTFont("DV-Oblique", str(font_dir / "DejaVuSans-Oblique.ttf")))
    pdfmetrics.registerFont(TTFont("DVM", str(font_dir / "DejaVuSansMono.ttf")))
    pdfmetrics.registerFont(TTFont("DVM-Bold", str(font_dir / "DejaVuSansMono-Bold.ttf")))
    pdfmetrics.registerFontFamily(
        "DV", normal="DV", bold="DV-Bold", italic="DV-Oblique", boldItalic="DV-Bold"
    )


register_fonts()


class ResearchDocTemplate(BaseDocTemplate):
    def __init__(self, filename: str, **kwargs) -> None:
        super().__init__(filename, **kwargs)
        frame = Frame(
            self.leftMargin,
            self.bottomMargin,
            self.width,
            self.height,
            leftPadding=0,
            rightPadding=0,
            topPadding=0,
            bottomPadding=0,
            id="body",
        )
        self.addPageTemplates(PageTemplate(id="research-note", frames=[frame], onPage=self.decorate))

    def decorate(self, canvas, doc) -> None:
        canvas.saveState()
        width, height = A4
        if doc.page > 1:
            canvas.setStrokeColor(RULE)
            canvas.setLineWidth(0.5)
            canvas.line(self.leftMargin, height - 13 * mm, width - self.rightMargin, height - 13 * mm)
            canvas.setFont("DV", 8)
            canvas.setFillColor(MUTED)
            canvas.drawString(self.leftMargin, height - 10 * mm, "Kempner function: sharp coprime-fiber obstruction")
            canvas.drawRightString(width - self.rightMargin, height - 10 * mm, "Research note | 2026-08-20")
        canvas.setStrokeColor(RULE)
        canvas.line(self.leftMargin, 12 * mm, width - self.rightMargin, 12 * mm)
        canvas.setFont("DV", 8)
        canvas.setFillColor(MUTED)
        canvas.drawString(self.leftMargin, 8 * mm, "Self-contained handoff for independent mathematical review")
        canvas.drawRightString(width - self.rightMargin, 8 * mm, f"Page {doc.page}")
        canvas.restoreState()


base = getSampleStyleSheet()
styles = {
    "title": ParagraphStyle(
        "Title",
        parent=base["Title"],
        fontName="DV-Bold",
        fontSize=24,
        leading=29,
        textColor=NAVY,
        alignment=TA_LEFT,
        spaceAfter=10,
    ),
    "subtitle": ParagraphStyle(
        "Subtitle",
        parent=base["Normal"],
        fontName="DV",
        fontSize=11.5,
        leading=16,
        textColor=MUTED,
        spaceAfter=12,
    ),
    "h1": ParagraphStyle(
        "H1",
        parent=base["Heading1"],
        fontName="DV-Bold",
        fontSize=16,
        leading=20,
        textColor=NAVY,
        spaceBefore=12,
        spaceAfter=7,
        keepWithNext=True,
    ),
    "h2": ParagraphStyle(
        "H2",
        parent=base["Heading2"],
        fontName="DV-Bold",
        fontSize=11.5,
        leading=15,
        textColor=BLUE,
        spaceBefore=9,
        spaceAfter=4,
        keepWithNext=True,
    ),
    "body": ParagraphStyle(
        "Body",
        parent=base["BodyText"],
        fontName="DV",
        fontSize=9.25,
        leading=13.1,
        textColor=INK,
        alignment=TA_LEFT,
        spaceAfter=6,
    ),
    "small": ParagraphStyle(
        "Small",
        parent=base["BodyText"],
        fontName="DV",
        fontSize=8.1,
        leading=11.1,
        textColor=MUTED,
        spaceAfter=4,
    ),
    "status_label": ParagraphStyle(
        "StatusLabel",
        parent=base["BodyText"],
        fontName="DV-Bold",
        fontSize=7.6,
        leading=9.5,
        textColor=WHITE,
        spaceAfter=0,
    ),
    "bullet": ParagraphStyle(
        "Bullet",
        parent=base["BodyText"],
        fontName="DV",
        fontSize=9.1,
        leading=12.6,
        textColor=INK,
        leftIndent=14,
        firstLineIndent=-9,
        bulletIndent=3,
        spaceAfter=4,
    ),
    "number": ParagraphStyle(
        "Number",
        parent=base["BodyText"],
        fontName="DV",
        fontSize=9.1,
        leading=12.6,
        textColor=INK,
        leftIndent=18,
        firstLineIndent=-13,
        spaceAfter=5,
    ),
    "formula": ParagraphStyle(
        "Formula",
        parent=base["BodyText"],
        fontName="DVM",
        fontSize=9.2,
        leading=13.2,
        textColor=NAVY,
        alignment=TA_CENTER,
        spaceBefore=4,
        spaceAfter=4,
    ),
    "formula_small": ParagraphStyle(
        "FormulaSmall",
        parent=base["BodyText"],
        fontName="DVM",
        fontSize=7.8,
        leading=10.8,
        textColor=NAVY,
        alignment=TA_LEFT,
        spaceBefore=2,
        spaceAfter=2,
    ),
    "box": ParagraphStyle(
        "Box",
        parent=base["BodyText"],
        fontName="DV",
        fontSize=9.2,
        leading=13.0,
        textColor=INK,
        spaceAfter=0,
    ),
    "caption": ParagraphStyle(
        "Caption",
        parent=base["BodyText"],
        fontName="DV-Oblique",
        fontSize=7.8,
        leading=10.5,
        textColor=MUTED,
        alignment=TA_CENTER,
        spaceAfter=5,
    ),
    "reference": ParagraphStyle(
        "Reference",
        parent=base["BodyText"],
        fontName="DV",
        fontSize=7.8,
        leading=10.7,
        textColor=INK,
        leftIndent=14,
        firstLineIndent=-14,
        spaceAfter=4,
    ),
}


def P(text: str, style: str = "body") -> Paragraph:
    return Paragraph(text, styles[style])


def H1(text: str) -> Paragraph:
    return P(text, "h1")


def H2(text: str) -> Paragraph:
    return P(text, "h2")


def bullet(text: str) -> Paragraph:
    return P(f"- {text}", "bullet")


def numbered(n: int, text: str) -> Paragraph:
    return P(f"{n}. {text}", "number")


def formula(text: str, shade=PALE_BLUE, align=TA_CENTER) -> Table:
    style = styles["formula"].clone(f"formula-{len(text)}")
    style.alignment = align
    table = Table([[Paragraph(text, style)]], colWidths=[165 * mm], hAlign="CENTER")
    table.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, -1), shade),
                ("BOX", (0, 0), (-1, -1), 0.65, RULE),
                ("LEFTPADDING", (0, 0), (-1, -1), 8),
                ("RIGHTPADDING", (0, 0), (-1, -1), 8),
                ("TOPPADDING", (0, 0), (-1, -1), 7),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 7),
            ]
        )
    )
    return table


def callout(title: str, text: str, shade=PALE_TEAL, accent=TEAL) -> Table:
    title_p = Paragraph(title, ParagraphStyle(
        f"callout-title-{title}", parent=styles["box"], fontName="DV-Bold", textColor=accent, spaceAfter=3
    ))
    body_p = P(text, "box")
    table = Table([[title_p], [body_p]], colWidths=[165 * mm], hAlign="CENTER")
    table.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (-1, -1), shade),
                ("LINEBEFORE", (0, 0), (0, -1), 3, accent),
                ("BOX", (0, 0), (-1, -1), 0.5, RULE),
                ("LEFTPADDING", (0, 0), (-1, -1), 10),
                ("RIGHTPADDING", (0, 0), (-1, -1), 10),
                ("TOPPADDING", (0, 0), (-1, 0), 7),
                ("BOTTOMPADDING", (0, 0), (-1, 0), 2),
                ("TOPPADDING", (0, 1), (-1, 1), 1),
                ("BOTTOMPADDING", (0, 1), (-1, 1), 8),
            ]
        )
    )
    return table


def status_table() -> Table:
    rows = [
        [P("PROVED", "status_label"), P("Sharp coprime-fiber inequality, local cross-exponent bounds, and infinite sharp family.", "small")],
        [P("FORMALIZED", "status_label"), P("Lean/Mathlib checks the actual Kempner graph predicate and the main global theorem.", "small")],
        [P("OPEN", "status_label"), P("The full Tuţescu conjecture S(n) != S(n+1) is not resolved.", "small")],
        [P("NOVELTY", "status_label"), P("Apparently new after an expanded database audit; historical novelty is not formally certifiable.", "small")],
    ]
    t = Table(rows, colWidths=[28 * mm, 137 * mm], hAlign="CENTER")
    t.setStyle(
        TableStyle(
            [
                ("BACKGROUND", (0, 0), (0, 1), NAVY),
                ("TEXTCOLOR", (0, 0), (0, 1), WHITE),
                ("BACKGROUND", (0, 2), (0, 2), AMBER),
                ("TEXTCOLOR", (0, 2), (0, 2), WHITE),
                ("BACKGROUND", (0, 3), (0, 3), TEAL),
                ("TEXTCOLOR", (0, 3), (0, 3), WHITE),
                ("BACKGROUND", (1, 0), (1, -1), colors.HexColor("#F7FAFC")),
                ("GRID", (0, 0), (-1, -1), 0.5, RULE),
                ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
                ("LEFTPADDING", (0, 0), (-1, -1), 7),
                ("RIGHTPADDING", (0, 0), (-1, -1), 7),
                ("TOPPADDING", (0, 0), (-1, -1), 6),
                ("BOTTOMPADDING", (0, 0), (-1, -1), 6),
            ]
        )
    )
    return t


def build_story():
    story = []

    story += [
        Spacer(1, 9 * mm),
        P("A SHARP COPRIME-FIBER OBSTRUCTION", "small"),
        P("for the Kempner function", "title"),
        P(
            "Self-contained theorem, proof, sharpness construction, consequence for the Tuţescu conjecture, "
            "formal verification record, computational audit, and bibliographic novelty assessment.",
            "subtitle",
        ),
        HRFlowable(width="100%", thickness=2, color=TEAL, spaceBefore=1, spaceAfter=13),
        status_table(),
        Spacer(1, 7 * mm),
        H2("One-sentence handoff"),
        callout(
            "Main result",
            "If two nontrivial coprime integers x and y have the same Kempner value m, then the common value is sharply constrained by the largest prime exponents in x and y: "
            "m + min(E(x),E(y)) &lt;= E(x)E(y). This forces every hypothetical consecutive-value counterexample into a square-root-scale smooth-number set.",
        ),
        Spacer(1, 5 * mm),
        H2("What this note does not claim"),
        bullet("It does not prove the full conjecture S(n) != S(n+1)."),
        bullet("Lean verification certifies mathematical derivations relative to Lean/Mathlib; it does not certify bibliographic novelty."),
        bullet("The computation validates the theorem and searches a large finite range; it is not used in the proof."),
        Spacer(1, 5 * mm),
        P("Audit date: 2026-08-20 | Workspace artifact: KempnerResearch", "small"),
        PageBreak(),
    ]

    story += [
        H1("1. Definitions and theorem"),
        P(
            "For an integer n &gt;= 1, the Kempner function (often called the Smarandache function in the later literature) is",
        ),
        formula("S(n) = min { m &gt;= 1 : n divides m! }"),
        P(
            "For a prime p, let v_p(z) be the exponent of p in z. For z &gt; 1 define",
        ),
        formula("E(z) = max { v_l(z) : l is prime and l divides z }<br/>Pplus(z) = largest prime factor of z"),
        H2("Global coprime-fiber theorem"),
        callout(
            "Theorem 1",
            "Let x,y &gt; 1 be coprime and suppose S(x)=S(y)=m. Then<br/><br/>"
            "<font name='DVM-Bold'>m + min(E(x),E(y)) &lt;= E(x)E(y).</font><br/><br/>"
            "Consequently,<br/><br/>"
            "<font name='DVM-Bold'>max(Pplus(x),Pplus(y)) + min(E(x),E(y)) &lt;= E(x)E(y).</font>",
        ),
        H2("Sharper local form"),
        P(
            "Choose controlling prime powers p^a || x and q^b || y such that S(p^a)=S(q^b)=m. "
            "The primes are distinct. If p&lt;q and m=pqc, then",
        ),
        formula("a &gt;= qc + 1,        b &gt;= pc."),
        P(
            "If the smaller controlling prime belongs to y, interchange x and y. No uniqueness assumption on a controlling prime power is needed.",
        ),
        H2("Equivalent fiber viewpoint"),
        P(
            "A fiber of S is a set S^(-1)(m). The theorem says that any two coprime members of the same nontrivial fiber must carry large, cross-coupled prime exponents. "
            "The extra +min term is essential and sharp.",
        ),
        PageBreak(),
    ]

    story += [
        H1("2. Proof of the coprime-fiber theorem"),
        H2("Step 1: reduce to activating prime powers"),
        P(
            "If z has prime-power factorization z = product l^e, then",
        ),
        formula("S(z) = max { S(l^e) : l^e || z }."),
        P(
            "Hence there exist p^a || x and q^b || y with S(p^a)=S(q^b)=m. Minimality of m gives",
        ),
        formula("v_p((m-1)!) &lt; a &lt;= v_p(m!),     v_q((m-1)!) &lt; b &lt;= v_q(m!)."),
        H2("Step 2: both activating primes divide the common value"),
        P(
            "If p did not divide m, multiplying (m-1)! by m would not change its p-adic valuation, contradicting the displayed strict-to-weak jump. Thus p divides m; similarly q divides m. "
            "Because x and y are coprime while p divides x and q divides y, p and q are distinct. Therefore pq divides m.",
        ),
        H2("Step 3: Legendre's formula gives cross-exponent bounds"),
        P("Assume p&lt;q and write m=pqc with c&gt;=1. Then"),
        formula(
            "v_p((m-1)!)<br/>"
            "&gt;= floor((m-1)/p) + floor((m-1)/p^2)<br/>"
            "&gt;= (qc-1) + 1 = qc."
        ),
        P(
            "The second floor contributes at least one because p^2&lt;m: indeed p&lt;q and c&gt;=1. Since a is strictly larger than v_p((m-1)!), this yields a&gt;=qc+1. Likewise,",
        ),
        formula("v_q((m-1)!) &gt;= floor((m-1)/q) = pc-1,   so b &gt;= pc."),
        H2("Step 4: multiply the cross-bounds"),
        P(
            "Put A=E(x) and B=E(y). In this orientation A&gt;=qc+1 and B&gt;=pc. Therefore",
        ),
        formula("(A-1)B &gt;= (qc)(pc) = pqc^2 = mc &gt;= m."),
        P(
            "Thus m+B&lt;=AB. Since min(A,B)&lt;=B, the first inequality of Theorem 1 follows. The other orientation is symmetric. Finally, x and y both divide m!, so each of their prime factors is at most m. Replacing m on the left by any such prime factor proves the Pplus consequence.",
        ),
        PageBreak(),
    ]

    story += [
        H1("3. Sharpness and equality"),
        P("Let p&lt;q&lt;2p be primes. Legendre's formula gives"),
        formula("v_p((pq-1)!) = q,       v_q((pq-1)!) = p-1."),
        P(
            "Multiplication by pq adds one copy of both primes. It follows that",
        ),
        formula("S(p^(q+1)) = S(q^p) = pq."),
        P(
            "The two inputs are coprime, E(p^(q+1))=q+1, E(q^p)=p, and",
        ),
        formula("pq + min(q+1,p) = pq+p = (q+1)p."),
        P(
            "So equality holds in Theorem 1. Bertrand's theorem supplies a prime q with p&lt;q&lt;2p for every prime p, giving infinitely many sharp pairs.",
        ),
        H2("Equality classification at controller level"),
        P(
            "Tracing equality through the proof shows that equality forces c=1, maximal exponents q+1 and p on the relevant sides, and q&lt;2p. The construction above proves these conditions sufficient. "
            "The smallest example is x=16, y=9, m=6.",
        ),
        H1("4. Consequence for the Tuţescu conjecture"),
        P(
            "The conjecture asserts S(n) != S(n+1) for every positive integer n. Consecutive integers are coprime. If a counterexample existed, Theorem 1 would imply",
        ),
        formula(
            "max(Pplus(n),Pplus(n+1))<br/>"
            "&lt;= E(n)E(n+1) - min(E(n),E(n+1))."
        ),
        P(
            "The local bounds also imply that one neighbor is divisible by a fourth power and the other by a square. Hence the theorem already excludes every pair with one squarefree member and every pair in which both members are fourth-power-free.",
        ),
        callout(
            "Important status",
            "This is a necessary condition for a counterexample, not a contradiction. For example, the consecutive pair 8,9 satisfies the factorization-only obstruction, but S(8)=4 and S(9)=6.",
            shade=PALE_AMBER,
            accent=AMBER,
        ),
        PageBreak(),
    ]

    story += [
        H1("5. Quantitative smooth-number reduction"),
        P(
            "Let C(X) count hypothetical Tuţescu counterexamples n&lt;=X. Since E(n),E(n+1)&lt;=log_2(X+1), the prime-factor inequality makes both n and n+1 Y-smooth with",
        ),
        formula("Y = (log_2(X+1))^2."),
        P("Consequently,"),
        formula("C(X) &lt;= Psi(X,Y) = X^(1/2+o(1))."),
        P(
            "Here Psi(X,Y) counts integers at most X whose prime factors are all at most Y. The final equality is the standard estimate Psi(X,(log X)^alpha)=X^(1-1/alpha+o(1)) with alpha=2. "
            "This is a power-saving structural reduction.",
        ),
        H2("Comparison with the normal-order route"),
        P(
            "The classical fact S(n)=Pplus(n) for almost all n only places counterexamples in a density-zero exceptional set. Ivić's sharper estimate for that exception set is of order",
        ),
        formula("X exp(-(sqrt(2)+o(1)) sqrt(log X log log X)) = X^(1-o(1))."),
        P("The new coprime-fiber obstruction instead gives X^(1/2+o(1))."),
        H1("6. Computational audit"),
        P("The proof is independent of computation. Two reproducible checks were run:"),
        numbered(
            1,
            "The activation audit enumerated 5,004,826 pairs of activating prime-power configurations with common value m&lt;=10^6. It found 0 violations, 8,097 sharp configurations, and 0 sharpness-classification mismatches.",
        ),
        numbered(
            2,
            "The consecutive sieve checked n&lt;=10^8. It found 0 equalities S(n)=S(n+1). Only 30 pairs survived the new factorization-only necessary condition, and direct Kempner values eliminated all 30.",
        ),
        H2("Exact reproduction commands"),
        formula(
            "lake build<br/>"
            "python3 scripts/audit_activations.py --max-value 1000000<br/>"
            "g++ -O3 -std=c++20 scripts/search_consecutive.cpp -o /tmp/search_consecutive<br/>"
            "/tmp/search_consecutive --limit 100000000",
            shade=colors.HexColor("#F5F6F7"),
            align=TA_LEFT,
        ),
        PageBreak(),
    ]

    story += [
        H1("7. Lean/Mathlib verification"),
        P(
            "The formalization uses an actual graph predicate IsKempnerValue x m, not an algebraic surrogate. It proves activation existence from a fiber witness, valuation-jump lemmas, cross-exponent bounds, and the global coprime theorem.",
        ),
        H2("Main checked declarations"),
        formula(
            "coprime_activated_fiber_bound<br/>"
            "coprime_kempner_fiber_bound<br/>"
            "coprime_kempner_fiber_bound_sub<br/>"
            "prime_factor_add_min_le_exponent_product",
            shade=colors.HexColor("#F5F6F7"),
            align=TA_LEFT,
        ),
        P(
            "Source: KempnerResearch/Basic.lean. The main theorem has hypotheses x,y&gt;1, IsKempnerValue x m, IsKempnerValue y m, and Nat.Coprime x y, and concludes",
        ),
        formula(
            "m + min (maxPrimeExponent x) (maxPrimeExponent y)<br/>"
            "  &lt;= maxPrimeExponent x * maxPrimeExponent y."
        ),
        P(
            "The project builds with Lean v4.34.0-rc1 and the Mathlib revision pinned in lake-manifest.json. From the repository root, the checked command is:",
        ),
        formula(
            "lake build",
            shade=colors.HexColor("#F5F6F7"),
            align=TA_LEFT,
        ),
        H1("8. Falsified stronger variants"),
        bullet("Strict inequality is false: x=16, y=9, m=6 gives equality."),
        bullet("Replacing E(x)E(y) by (E(x)-1)(E(y)-1) is false for the same pair."),
        bullet("Replacing the local lower bound qc+1 by qc+2 is false for p=2, q=3, c=1."),
        bullet("The smoothness obstruction alone does not settle adjacency: 8,9 survives it."),
        callout(
            "Interpretation",
            "These failures are useful boundary data. They show that the +min term, the extra single p-adic copy, and the distinction between a necessary structural filter and a proof of the conjecture are all genuine.",
        ),
        PageBreak(),
    ]

    story += [
        H1("9. Expanded novelty audit"),
        H2("zbMATH Open (Zentralblatt): direct database coverage"),
        bullet("257 records contain the exact phrase 'Smarandache function' in an indexed field; 155 match in titles and 174 in reviews or summaries."),
        bullet("Seven records match Tutescu or Tuţescu; the number-theoretic conjecture paper is MR1650388 / Zbl 1008.11508."),
        bullet("All 12 review/summary records containing both 'Smarandache function' and 'S(n+1)' were screened."),
        bullet(
            "Review/summary queries also combined the function name with Legendre, valuation, p-adic, exponent, prime power, same value, equal values, fiber, preimage, inverse image, smooth, coprime, maximal exponent, and maximum exponent. Plausible hits were inspected."
        ),
        bullet("No indexed review or summary states the coprime-fiber inequality, its local qc+1/pc bounds, its sharp family, or the X^(1/2+o(1)) consequence."),
        bullet("The indexed reference-text search found no citation under Prodanescu, Tutescu, or the exact conjecture-paper title; that index has incomplete reference coverage."),
        H2("MathSciNet: public coverage and limitation"),
        P(
            "Full MathSciNet Anywhere, Review Text, and References searching redirected to institutional authentication in this environment. The public MR Lookup service was searched instead. Because it returns at most three regular results per query, 'Smarandache function' was queried separately for every year 1980-2026 and supplemented with targeted title conjunctions.",
        ),
        bullet("The year-sliced public search produced 51 distinct MR records."),
        bullet("There were no title hits coupling the function with consecutive, equal, equality, fiber, inverse, or exponent."),
        bullet("The three coprime title hits concern a distinct 0-1 characteristic function, not coprime inputs sharing a Kempner value."),
        bullet("Exact searches recovered the main known records and authors, including MR1650388, MR1364859, MR1416986, MR1294796, and the three editions/versions MR1294791, MR1361855, MR1398974."),
        H2("Nearest prior results found"),
        P(
            "Ashbacher observes that if equal values are written kp=rq using activating primes from the two coprime inputs, then q divides k and p divides r. Prodanescu and Tutescu prove the weaker fact that an input and its Kempner value share a prime factor. Neither source obtains the extra Legendre copy for the smaller prime or a global exponent-product bound.",
        ),
        callout(
            "Novelty conclusion",
            "The theorem is proved and the expanded audit supports 'apparently novel.' It is still not 'certified novel': the MathSciNet search was not subscriber-level full text, database indexing can be incomplete, terminology varies, and an expert referee could locate an equivalent result.",
            shade=PALE_AMBER,
            accent=AMBER,
        ),
        PageBreak(),
    ]

    story += [
        H1("10. Independent-review checklist"),
        P("A second model or human referee should try to break the result at these points:"),
        numbered(1, "Verify the max-over-prime-powers identity supplies at least one activating component on each side without assuming uniqueness."),
        numbered(2, "Check that activation at m forces the activating prime to divide m, and that coprimality forces the two activating primes to differ."),
        numbered(3, "Check the extra floor term floor((m-1)/p^2)&gt;=1 when p&lt;q and m=pqc; this is the source of qc+1 rather than qc."),
        numbered(4, "Trace every equality condition in (A-1)B&gt;=mc&gt;=m and verify the p&lt;q&lt;2p construction."),
        numbered(5, "Check that the Pplus bound follows because x and y divide m!, then verify the smooth-number counting exponent 1/2."),
        numbered(6, "Run a subscriber-level MathSciNet Anywhere/Review Text/References search and search non-indexed Smarandache Function Journal archives for differently phrased equivalents."),
        H1("References and stable identifiers"),
        P(
            "[1] I. Prodanescu and L. Tutescu, <i>On a conjecture concerning the Smarandache function</i>, Smarandache Notions J. 9 (1998), 104-105. MR1650388; Zbl 1008.11508. "
            "<link href='https://fs.unm.edu/SNJ/OnAConjectureConcerning-9.pdf' color='#246B8E'>Full text</link>.",
            "reference",
        ),
        P(
            "[2] C. Ashbacher, <i>An introduction to the Smarandache function</i>, Erhus University Press, 1995. MR1364859; Zbl 0834.11002. "
            "<link href='https://fs.unm.edu/SF/AnIntroduction.pdf' color='#246B8E'>Full text</link>.",
            "reference",
        ),
        P(
            "[3] A. A. Mullin, <i>On the Smarandache function and the fixed-point theory of numbers</i>, Smarandache Notions J. 7 (1996), 107. MR1416986; Zbl 0885.11012.",
            "reference",
        ),
        P(
            "[4] A. Ivić, <i>On a problem of Erdős involving the largest prime factor of n</i>, Monatsh. Math. 145 (2005), 35-46. Zbl 1098.11046. "
            "<link href='https://arxiv.org/abs/math/0311056' color='#246B8E'>arXiv</link>.",
            "reference",
        ),
        P(
            "[5] A. Hildebrand and G. Tenenbaum, <i>On integers free of large prime factors</i>, Trans. Amer. Math. Soc. 296 (1986), 265-290. "
            "<link href='https://jtnb.centre-mersenne.org/articles/10.5802/jtnb.101/' color='#246B8E'>Related survey source</link>.",
            "reference",
        ),
        P(
            "[6] <link href='https://zbmath.org/' color='#246B8E'>zbMATH Open</link> and "
            "<link href='https://mathscinet.ams.org/mrlookup' color='#246B8E'>MathSciNet MR Lookup</link>, database audit performed 2026-08-20.",
            "reference",
        ),
        Spacer(1, 4 * mm),
        callout(
            "Machine-readable bottom line",
            "PROVED: for coprime x,y&gt;1 with S(x)=S(y)=m, m+min(E(x),E(y))&lt;=E(x)E(y), sharply. CONSEQUENCE: hypothetical S(n)=S(n+1) values up to X form a set of size at most X^(1/2+o(1)). OPEN: existence is not ruled out. NOVELTY: apparently new after the stated audit, not historically certified.",
        ),
    ]
    return story


def main() -> None:
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    doc = ResearchDocTemplate(
        str(OUTPUT),
        pagesize=A4,
        leftMargin=21 * mm,
        rightMargin=21 * mm,
        topMargin=18 * mm,
        bottomMargin=17 * mm,
        title="A sharp coprime-fiber obstruction for the Kempner function",
        author="Research artifact; authorship not assigned",
        subject="Kempner function, coprime fibers, Tutescu conjecture, Lean formalization",
        keywords="Kempner function, Smarandache function, Tutescu conjecture, p-adic valuation, smooth numbers, Lean",
    )
    doc.build(build_story())
    print(OUTPUT)


if __name__ == "__main__":
    main()
