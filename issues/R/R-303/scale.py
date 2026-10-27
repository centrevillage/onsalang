import sys,subprocess,time,os
onsa=sys.argv[1]; kind=sys.argv[2]
for N in map(int,sys.argv[3:]):
    cyc="".join(f"type C{i} = C{(i+1)%N}\n" for i in range(N))
    tail={"impl":"impl C0 { pub fn q() -> I32 { 1 } }\n","typ":"pub fn f(x: C0) -> I32 { 1 }\n","len":"pub fn f(x: [F32; C0.N]) -> I32 { 1 }\n","none":""}[kind]
    f=f"/private/tmp/claude-501/-Users-centrevillage-projects-onsalang/4945602c-a0a4-48b9-8fbb-e70e5c822003/scratchpad/w404/u8b/b/scale_{kind}.onsa"
    open(f,"w").write(cyc+tail)
    t=time.time()
    try:
        r=subprocess.run([onsa,"check",f],capture_output=True,text=True,timeout=40)
        print(kind,N,r.returncode,"%.2fs"%(time.time()-t),flush=True)
    except subprocess.TimeoutExpired:
        print(kind,N,"TIMEOUT",flush=True)
