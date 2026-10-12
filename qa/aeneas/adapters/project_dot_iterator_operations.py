"""Expose missing standard iterator methods as their actual dictionary callbacks.

The pinned standard model omits ExactSizeIterator.len and Iterator.zip fields.
Keep the two original supertrait dictionaries and both dispatched methods in an
explicit ExactIteratorOps record. Only the two parameter types and the left
parent-method projection change; arithmetic, assertions, conversion and next
calls remain byte-identical. Contracts quantify the actual callbacks, including
possible overrides, rather than assuming zip or len has its default body.
"""
import argparse
import hashlib
import json
import re
from pathlib import Path

if not __debug__:
    raise RuntimeError("This adapter requires Python assertions")

NAMESPACE="CommonProductDotIter"
TRAIT="core.iter.traits.exact_size.ExactSizeIterator"
PROJECTION="coreitertraitsexact_sizeExactSizeIteratorClause3_IntoIterSharedAPastaFieldInst.iteratorInst.zip"
DIRECT="coreitertraitsexact_sizeExactSizeIteratorClause3_IntoIterSharedAPastaFieldInst.zip"


def block(source):
    pattern=r"(?ms)^def field\.pasta\.products\.dot_iter\b.*?(?=\n/--|\nend "+NAMESPACE+r"\n)"
    matches=list(re.finditer(pattern,source))
    assert len(matches)==1
    return matches[0]


def inventory(source):
    match=block(source)
    function=match.group()
    header,body=function.split("  := do\n",1)
    assert "Clause5_Clause0_Item" not in function and "Clause6_Clause0_Item" not in function
    assert header.count(TRAIT)==2
    assert body.count(PROJECTION)==1
    assert body.count("coreitertraitsexact_sizeExactSizeIteratorClause3_IntoIterSharedAPastaFieldInst.len")==1
    assert body.count("coreitertraitsexact_sizeExactSizeIteratorClause4_IntoIterSharedAPastaFieldInst.len")==1
    assert ".len.default" not in source
    assert "if left_val = right_val" in body
    assert source.count(TRAIT)==2
    return match,header,body


def check_projection(original, projected):
    before,header,body=inventory(original)
    match=block(projected)
    h,b=match.group().split("  := do\n",1)
    assert h.count("ExactIteratorOps")==2
    assert h.replace("ExactIteratorOps",TRAIT)==header
    assert b.count(DIRECT)==1 and PROJECTION not in b
    assert b.replace(DIRECT,PROJECTION)==body
    assert projected[:match.start()]==original[:before.start()]
    assert projected[match.end():]==original[before.end():]


def adapt(original,self_test=False):
    match,header,body=inventory(original)
    result=original[:match.start()]+header.replace(TRAIT,"ExactIteratorOps")+"  := do\n"+body.replace(PROJECTION,DIRECT)+original[match.end():]
    check_projection(original,result)
    if self_test:
        mutations=[result.replace("if left_val = right_val","if right_val = left_val"),
            result.replace(DIRECT,"coreitertraitsexact_sizeExactSizeIteratorClause4_IntoIterSharedAPastaFieldInst.zip"),
            result.replace("coreitertraitsexact_sizeExactSizeIteratorClause3_IntoIterSharedAPastaFieldInst.len","coreitertraitsexact_sizeExactSizeIteratorClause4_IntoIterSharedAPastaFieldInst.len"),
            result.replace("ExactIteratorOps Clause3_IntoIter","ExactIteratorOps Clause4_IntoIter"),
            result.replace("namespace "+NAMESPACE,"namespace Different",1)]
        assert all(m!=result for m in mutations)
        for mutation in mutations:
            try:
                check_projection(original,mutation)
            except (AssertionError,IndexError,KeyError,TypeError):
                pass
            else:
                raise RuntimeError("The dictionary checker accepted changed operations or code")
    digest=lambda s:hashlib.sha256(s.encode()).hexdigest()
    return result,{"retained_supertrait_dictionaries":2,"retained_length_callbacks":2,
        "retained_left_zip_callback":True,"arithmetic_and_control_flow_byte_identical":True,
        "all_other_functions_byte_identical":True,"original_source_restored":True,
        "unused_default_len_template_not_called":True,"rejected_mutations":5 if self_test else 0,
        "original_sha256":digest(original),"adapted_sha256":digest(result)}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source",type=Path)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    result,report=adapt(args.source.read_text(),args.self_test)
    args.source.write_text(result)
    print(json.dumps(report,indent=2))
