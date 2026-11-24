#!/usr/bin/env python3
"""Render the assessment with its summary on page 1 and details from page 2.

Requires installed Pandoc, pdfLaTeX, and Poppler. This formats existing review
results; it does not run Lean or add mathematical verification claims.
"""
import argparse
from pathlib import Path
import re
import shutil
import subprocess
from urllib.parse import quote, urlsplit


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-commit', required=True)
    args = parser.parse_args()
    if not re.fullmatch(r'[0-9a-f]{40}', args.evidence_commit):
        parser.error('--evidence-commit must be a full Git commit')
    repo = Path(__file__).resolve().parents[1]
    work = repo / 'work/assessment-pdf'
    work.mkdir(parents=True, exist_ok=True)
    source = repo / 'docs/assessment.md'
    markdown = source.read_text()
    marker = '<!-- end-one-page-summary -->'
    assert markdown.count(marker) == 1
    summary, details = markdown.split(marker)
    base = 'https://github.com/yang-mills-group/QCD/blob/' + args.evidence_commit + '/'

    def link(match):
        label, target = match.groups()
        if urlsplit(target).scheme or target.startswith('#'):
            return match[0]
        name, separator, anchor = target.partition('#')
        path = (source.parent / name).resolve()
        assert path.is_file(), target
        relative = path.relative_to(repo).as_posix()
        return '[' + label + '](' + base + quote(relative, safe='/') + ('#' + anchor if separator else '') + ')'

    markdown = re.sub(r'\[([^\]]*)\]\(([^)]+)\)', link, markdown)
    markdown = markdown.replace(marker, '\\clearpage')
    markdown = markdown.replace('# Massive QCD: verification assessment\n\n20 November 2026 | Summary of results and checks', r'''\begin{center}
{\Large\bfseries Massive QCD: verification assessment}\par
{\normalsize Summary of results and checks\quad\textbullet\quad20 November 2026}
\end{center}''', 1)
    markdown += '\n\n**Evidence snapshot.** '
    markdown += ('Links to supporting records use repository revision `'
                 + args.evidence_commit[:12] + '`. This editorial revision changes no mathematical '
                 'source or recorded verdict.\n')
    (work/'assessment-input.md').write_text(markdown)
    header = r'''\usepackage{fancyhdr,enumitem,xurl,microtype,needspace,etoolbox}
\setlength{\parindent}{0pt}
\setlength{\parskip}{5pt plus 1pt}
\setlength{\headheight}{14pt}
\setlength{\emergencystretch}{2em}
\clubpenalty=10000
\widowpenalty=10000
\setlist{leftmargin=1.4em,itemsep=2pt,topsep=3pt}
\pretocmd{\subsection}{\Needspace{7\baselineskip}}{}{}
\pretocmd{\subsubsection}{\Needspace{12\baselineskip}}{}{}
\pagestyle{plain}
\AtBeginDocument{\hypersetup{pdftitle={Massive QCD: verification assessment},
pdfauthor={Review prepared with Codex},linkcolor=blue!45!black,urlcolor=blue!45!black}}
'''
    (work/'header.tex').write_text(header)
    (work/'format.lua').write_text(r'''function Code(el)
  local text = el.text:gsub('–', '-'):gsub('—', '-')
  local parts = {}
  for token in text:gmatch('%S+') do
    table.insert(parts, '\\nolinkurl{' .. token .. '}')
  end
  return pandoc.RawInline('latex', '{\\small ' .. table.concat(parts, '\\ ') .. '}')
end
function Table(el)
  if #el.colspecs == 2 then
    el.colspecs[1][2] = 0.30
    el.colspecs[2][2] = 0.70
  end
  return el
end
''')
    tex = work/'qcd-verification-assessment.tex'
    subprocess.run([
        'pandoc', str(work/'assessment-input.md'), '-f', 'markdown+tex_math_dollars+raw_tex',
        '-t', 'latex', '--standalone', '--include-in-header', str(work/'header.tex'),
        '--lua-filter', str(work/'format.lua'),
        '-V', 'documentclass=article', '-V', 'fontsize=11pt', '-V', 'fontfamily=lmodern',
        '-V', 'geometry=letterpaper,margin=0.8in', '-V', 'colorlinks=true',
        '-o', str(tex),
    ], check=True)
    # Keep a portable, complete source rather than an input-dependent wrapper.
    shutil.copy2(tex, repo/'docs/qcd-verification-assessment.tex')
    for number in range(2):
        result = subprocess.run([
            'pdflatex', '-interaction=nonstopmode', '-halt-on-error', '-file-line-error',
            '-output-directory', str(work), str(tex),
        ], cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (work/f'compile-{number+1}.log').write_text(result.stdout)
        if result.returncode:
            print(result.stdout[-6000:])
            raise SystemExit(result.returncode)
    pdf = work/'qcd-verification-assessment.pdf'
    subprocess.run(['pdftotext', '-layout', str(pdf), str(work/'assessment-layout.txt')], check=True)
    pages = (work/'assessment-layout.txt').read_text().split('\f')
    if not pages[-1].strip():
        pages.pop()
    assert len(pages) > 1
    assert 'Detailed assessment' not in pages[0], 'Details leaked onto summary page'
    assert 'Derivation of the physical two-loop coefficient is deferred' in ' '.join(pages[0].split()), 'Summary overflowed'
    assert 'Detailed assessment' in pages[1], 'Details must begin on page 2'
    bad = re.findall(r'(?m)^.*(?:Overfull|Missing character|LaTeX Warning).*$'
                     , (work/'qcd-verification-assessment.log').read_text())
    if bad:
        print('\n'.join(bad))
        raise SystemExit('Resolve document warnings before publication')
    shutil.copy2(pdf, repo/'docs/qcd-verification-assessment.pdf')
    print(f'Compiled {len(pages)} pages; complete summary on page 1; details begin on page 2.')
    print('Render and visually inspect every page before delivery.')


if __name__ == '__main__':
    main()
