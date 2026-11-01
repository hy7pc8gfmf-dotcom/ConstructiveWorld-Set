# -*- coding: utf-8 -*-
"""ConstructiveWorld 全树去注释审计（铁律 5：计数必须先剥离嵌套块注释）"""
import re, sys, os, glob, json
from pathlib import Path

def strip_comments(text):
    """剥离 Coq 嵌套块注释 (* ... *)，保留行结构（注释内容替换为等长空白）"""
    out = []
    depth = 0
    i = 0
    n = len(text)
    buf = []
    while i < n:
        if text.startswith('(*', i):
            depth += 1
            buf.append('  ')
            i += 2
            continue
        if text.startswith('*)', i) and depth > 0:
            depth -= 1
            buf.append('  ')
            i += 2
            continue
        c = text[i]
        if depth > 0:
            buf.append('\n' if c == '\n' else ' ')
        else:
            buf.append(c)
        i += 1
    return ''.join(buf)

def strip_strings(text):
    """剥离双引号字符串内容（Coq 字符串）"""
    return re.sub(r'"(?:[^"]|"")*"', lambda m: '"' * len(m.group(0)), text)

DECL = r'(?m)^[ \t]*(?:Lemma|Theorem|Corollary|Fact|Remark|Example|Proposition|Instance|Definition|Fixpoint|CoFixpoint|Inductive|Record|Class|Structure|Variant)[ \t]+'

def main(root):
    stats = {
        'files': 0, 'lines': 0,
        'decl': 0, 'Qed': 0, 'Defined': 0, 'Admitted': 0, 'Abort': 0, 'admit_tac': 0,
        'Axiom': 0, 'Parameter': 0, 'Conjecture': 0, 'Hypothesis': 0, 'Variable': 0,
        'Context': 0, 'Classical_prop': 0, 'excluded_middle': 0, 'PEM': 0,
        'Obj_magic': 0, 'Instance': 0,
    }
    per_file = {}
    bad = []
    files = sorted(glob.glob(os.path.join(root, '*.v')))
    for f in files:
        raw = open(f, encoding='utf-8', errors='replace').read()
        code = strip_strings(strip_comments(raw))
        stats['files'] += 1
        stats['lines'] += raw.count('\n') + 1
        m = {
            'decl': len(re.findall(DECL, code)),
            'Qed': len(re.findall(r'\bQed\s*\.', code)),
            'Defined': len(re.findall(r'\bDefined\s*\.', code)),
            'Admitted': len(re.findall(r'\bAdmitted\s*\.', code)),
            'Abort': len(re.findall(r'\bAbort\s*\.', code)),
            'admit_tac': len(re.findall(r'(?<![\w.])admit\b(?!\w)', code)),
            'Axiom': len(re.findall(r'(?m)^[ \t]*Axiom\b', code)),
            'Parameter': len(re.findall(r'(?m)^[ \t]*Parameter\b', code)),
            'Conjecture': len(re.findall(r'(?m)^[ \t]*Conjecture\b', code)),
            'Hypothesis': len(re.findall(r'(?m)^[ \t]*Hypothesis\b', code)),
            'Variable': len(re.findall(r'(?m)^[ \t]*Variable\b', code)),
            'Context': len(re.findall(r'(?m)^[ \t]*Context\b', code)),
            'Classical_prop': len(re.findall(r'Classical_Prop\.classic|Coq\.Logic\.Classical', code)),
            'excluded_middle': len(re.findall(r'excluded_middle', code)),
            'PEM': len(re.findall(r'\bclassic\b', code)),
            'Obj_magic': len(re.findall(r'Obj\.magic', code)),
            'Instance': len(re.findall(r'(?m)^[ \t]*(?:Local |Global |#\[[^\]]*\]\s*)*Instance\b', code)),
        }
        per_file[os.path.basename(f)] = m
        for k, v in m.items():
            stats[k] += v
        if m['Admitted'] or m['Abort'] or m['admit_tac'] or m['Axiom'] or m['Parameter'] or m['Conjecture']:
            bad.append((os.path.basename(f), {k: m[k] for k in ('Admitted','Abort','admit_tac','Axiom','Parameter','Conjecture') if m[k]}))

    print('=' * 68)
    print('ConstructiveWorld 去注释权威审计')
    print('=' * 68)
    print(f"扫描文件数        : {stats['files']}")
    print(f"源码总行数        : {stats['lines']:,}")
    print('-' * 68)
    print(f"声明类（含 Instance/Definition）: {stats['decl']:,}")
    print(f"  Qed.            : {stats['Qed']:,}")
    print(f"  Defined.        : {stats['Defined']:,}")
    print(f"  Admitted.       : {stats['Admitted']}")
    print(f"  Abort.          : {stats['Abort']}")
    print(f"  admit 策略      : {stats['admit_tac']}")
    print(f"  闭合配平(声明=Qed+Defined+Admitted+Abort): {stats['decl'] - (stats['Qed']+stats['Defined']+stats['Admitted']+stats['Abort'])}")
    print('-' * 68)
    print('公理/假设面：')
    print(f"  Axiom           : {stats['Axiom']}")
    print(f"  Parameter       : {stats['Parameter']}")
    print(f"  Conjecture      : {stats['Conjecture']}")
    print(f"  Classical_Prop.classic / Coq.Logic.Classical : {stats['Classical_prop']}")
    print(f"  excluded_middle : {stats['excluded_middle']}")
    print(f"  classic (裸)    : {stats['PEM']}")
    print(f"  Obj.magic       : {stats['Obj_magic']}")
    print('-' * 68)
    print('Section 机制（用于假设封装判定）：')
    print(f"  Variable        : {stats['Variable']}")
    print(f"  Context         : {stats['Context']}")
    print(f"  Hypothesis      : {stats['Hypothesis']}")
    print(f"  Instance        : {stats['Instance']}")
    print('=' * 68)
    if bad:
        print('⚠ 含有非零禁用项的文件：')
        for b in bad:
            print('  ', b[0], b[1])
    else:
        print('✅ 去注释后：Admitted / Abort / admit / Axiom / Parameter / Conjecture 全部为 0')
    (Path(os.path.join(root, '..', '_tmpc', 'audit.json')).resolve()).write_text(json.dumps({'stats': stats, 'per_file': per_file}, ensure_ascii=False, indent=1), encoding='utf-8')

if __name__ == '__main__':
    main(sys.argv[1])
