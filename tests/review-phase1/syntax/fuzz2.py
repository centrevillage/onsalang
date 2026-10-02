import random, subprocess, glob, shutil
random.seed(7)
O="/Users/centrevillage/projects/onsalang/target/debug/onsa"
files=[f for f in glob.glob("/Users/centrevillage/projects/onsalang/tests/spec/**/*.onsa", recursive=True)]
bad=[]
for it in range(300):
    f=random.choice(files)
    src=open(f,encoding='utf-8').read()
    if src.startswith('//! mode: none') or '//~' in src: continue
    lines=src.split('\n')
    i=random.randrange(len(lines))
    mode=random.random()
    if mode<0.5:
        lines[i]=lines[i]+' // note'
    elif mode<0.8:
        # insert spaces around random place
        l=lines[i]
        if l:
            k=random.randrange(len(l)); lines[i]=l[:k]+'  '+l[k:]
    else:
        lines.insert(i,'// standalone')
    m='\n'.join(lines)
    a=f"fuzz2/a{it}.onsa"; b=f"fuzz2/b{it}.onsa"
    open(a,'w').write(m); open(b,'w').write(m)
    r0=subprocess.run([O,"check",a],capture_output=True,text=True)
    r=subprocess.run([O,"fmt",b],capture_output=True,text=True)
    if r.returncode!=0: continue
    d=subprocess.run([O,"diff","--ast",a,b],capture_output=True,text=True)
    if d.returncode!=0:
        bad.append((a,b,d.stdout.strip()[:200]))
for x in bad[:15]: print(x)
print(len(bad))
