import os, random, subprocess, glob, sys
random.seed(1)
O="/Users/centrevillage/projects/onsalang/target/debug/onsa"
files=[f for f in glob.glob("/Users/centrevillage/projects/onsalang/tests/spec/**/*.onsa", recursive=True)]
inserts=['{','}','(',')','"','\'','\\','音','\n','~','!','..','=','->',' ','.','_','//','///','0x','1.','@','#','|','&','é']
crashes={}
n=0
for it in range(600):
    f=random.choice(files)
    src=open(f,encoding='utf-8').read()
    if src.startswith('//! mode: none') or not src: continue
    chars=list(src)
    pos=random.randrange(len(chars))
    op=random.random()
    if op<0.4: chars.insert(pos, random.choice(inserts))
    elif op<0.7: del chars[pos]
    else:
        q=min(len(chars),pos+random.randrange(1,20)); del chars[pos:q]
    m=''.join(chars)
    p=f"fuzz/case{it}.onsa"
    open(p,'w',encoding='utf-8').write(m)
    for cmd in (["check",p],["fmt","--check",p]):
        r=subprocess.run([O]+cmd,capture_output=True,text=True)
        n+=1
        if r.returncode==101:
            msg=[l for l in r.stderr.splitlines() if 'panicked' in l]
            key=msg[0] if msg else r.stderr[:100]
            crashes.setdefault(key,[]).append((cmd[0],p))
for k,v in crashes.items():
    print(k, len(v), v[:2])
print("runs",n)
