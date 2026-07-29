# Local MSC2020 Archive

This directory contains the official Mathematics Subject Classification 2020
(MSC2020) distributions and derived files that make local searching easier.

Source: https://msc2020.org/

Downloaded: 2026-07-30

License: CC BY-NC-SA

## Files

- `MSC_2020.pdf`: The complete official 224-page document.
- `MSC_2020.tex`: The official LaTeX source.
- `MSC_2020.csv`: The official table. Despite the CSV extension, its columns
  are tab-separated and its source encoding is ISO-8859-1.
- `MSC_2020.utf8.tsv`: A search-friendly UTF-8 conversion of the official
  table with no content changes.
- `MSC_2020.txt`: Plain text extracted from the PDF with layout preserved.

The downloaded official table contains 6,603 classification records after its
header row.

## Quick Search

From the repository root:

```bash
# All Computer Science (68) codes
rg '^"68' references/msc2020/MSC_2020.utf8.tsv

# One specific code
rg '^"68Q15"' references/msc2020/MSC_2020.utf8.tsv

# Search descriptions for words or phrases
rg -i 'randomized algorithms|probabilistic' \
  references/msc2020/MSC_2020.utf8.tsv

# Search the full text
rg -n -i 'open problems' references/msc2020/MSC_2020.txt
```

`MSC_2020.utf8.tsv` can also be opened in any text or spreadsheet editor. Its
columns are `code`, `text`, and `description`, in that order.

## SHA-256 Checksums of Official Source Files

```text
532d86f87b042b1fbc30b72be174c98db8d2fb8e28b4150733956998363bcbe7  MSC_2020.pdf
ff79ec3154920b4515408ddb45c57dc4f1578e2ab109851a25fa20dfa37f9d3b  MSC_2020.tex
f7c889354c202551fe01f89bad2ae95ccadec4c57ac1f6f9de38bbd658d3c78c  MSC_2020.csv
```
