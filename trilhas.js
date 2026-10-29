/* DesmontAR 2.0 — protótipo de trilhas
 * Equipe: Ana Luísa, Ana Roberta, Giovanna e Luiza (UFPB)
 * Mapa de trilhas no estilo Duolingo, fases curtas com estrelas e RA com o mesmo marcador do DesmontAR. */
(function(){
const $=s=>document.querySelector(s);
const PI=Math.PI;
const reduceMotion=matchMedia('(prefers-reduced-motion: reduce)').matches;

/* ---------- cena 3D ---------- */
const renderer=new THREE.WebGLRenderer({antialias:true,alpha:true});
renderer.setPixelRatio(Math.min(devicePixelRatio||1,2));renderer.outputEncoding=THREE.sRGBEncoding;
$('#stage').appendChild(renderer.domElement);
const scene=new THREE.Scene();const BG=new THREE.Color(0x1b2330);scene.background=BG;
const camera=new THREE.PerspectiveCamera(45,1,.05,100);
const controls=new THREE.OrbitControls(camera,renderer.domElement);
controls.enableDamping=true;controls.maxPolarAngle=1.32;controls.minDistance=2.2;controls.maxDistance=11;controls.enablePan=false;
scene.add(new THREE.HemisphereLight(0xf4f7ff,0x30343c,.95));
const sun=new THREE.DirectionalLight(0xffffff,.85);sun.position.set(3,6,4);scene.add(sun);
const fill=new THREE.DirectionalLight(0x9fc4ff,.3);fill.position.set(-4,3,-2);scene.add(fill);
const video=$('#video');

/* ---------- marcador DesmontAR: mesmo detector do jogo original ---------- */
const CAM={on:false,seen:-1e9,cv:document.createElement('canvas'),fr:.8,tp:new THREE.Vector3(),tq:new THREE.Quaternion(),has:false,last:null,found:0,lastOk:0};
CAM.ctx=CAM.cv.getContext('2d',{willReadFrequently:true});
const cvG=new CV.Image(),cvT=new CV.Image(),cvB=[];
const MKBITS=(()=>{let s=3;const r=()=>{s=(s*9301+49297)%233280;return s/233280};const b=[];for(let y=0;y<8;y++)for(let x=0;x<8;x++)b.push(r()<.45?1:0);return b;})();
const mAW=new THREE.Matrix4().set(1,0,0,0, 0,0,-1,0, 0,1,0,0, 0,0,0,1);
function hsolve(A,b){const n=b.length;for(let i=0;i<n;i++){let p=i;for(let r=i+1;r<n;r++)if(Math.abs(A[r][i])>Math.abs(A[p][i]))p=r;[A[i],A[p]]=[A[p],A[i]];[b[i],b[p]]=[b[p],b[i]];
  if(Math.abs(A[i][i])<1e-12)return null;for(let r=i+1;r<n;r++){const k=A[r][i]/A[i][i];for(let c=i;c<n;c++)A[r][c]-=k*A[i][c];b[r]-=k*b[i];}}
  const x=new Array(n);for(let i=n-1;i>=0;i--){let v=b[i];for(let c=i+1;c<n;c++)v-=A[i][c]*x[c];x[i]=v/A[i][i];}return x;}
function homog(src,dst){const A=[],b=[];for(let i=0;i<4;i++){const [X,Y]=src[i],[x,y]=dst[i];A.push([X,Y,1,0,0,0,-x*X,-x*Y]);b.push(x);A.push([0,0,0,X,Y,1,-y*X,-y*Y]);b.push(y);}
  const h=hsolve(A,b);return h&&[[h[0],h[1],h[2]],[h[3],h[4],h[5]],[h[6],h[7],1]];}
const UNIT=[[0,0],[1,0],[1,1],[0,1]];
function hp(H,u,v){const w=H[2][0]*u+H[2][1]*v+H[2][2];return [(H[0][0]*u+H[0][1]*v+H[0][2])/w,(H[1][0]*u+H[1][1]*v+H[1][2])/w];}
function gAt(g,w,h,H,u,v){const [x,y]=hp(H,u,v);const xi=Math.round(x),yi=Math.round(y);if(xi<1||yi<1||xi>=w-1||yi>=h-1)return -1;
  const i=yi*w+xi;return (g[i]*2+g[i-1]+g[i+1]+g[i-w]+g[i+w]+g[i-w-1]+g[i-w+1]+g[i+w-1]+g[i+w+1])/10;}
function readMarker(g,w,h,c){
  const H=homog(UNIT,c.map(p=>[p.x,p.y]));if(!H)return null;
  let ring=0,nr=0,white=0,nw=0;
  for(let k=.08;k<.95;k+=.12)for(const [u,v] of [[k,.05],[k,.95],[.05,k],[.95,k]]){const q=gAt(g,w,h,H,u,v);if(q<0)return null;ring+=q;nr++;}
  for(const [u,v] of [[.15,.15],[.85,.15],[.15,.72],[.85,.72],[.5,.14],[.14,.5],[.86,.5]]){const q=gAt(g,w,h,H,u,v);if(q<0)return null;white+=q;nw++;}
  ring/=nr;white/=nw;if(white-ring<25)return null;const th=(ring+white)/2;
  let best=99,rot=0;
  for(let r=0;r<4;r++){const q=[c[r],c[(r+1)%4],c[(r+2)%4],c[(r+3)%4]];const Hr=homog(UNIT,q.map(p=>[p.x,p.y]));if(!Hr)continue;let d=0;
    for(let y=0;y<8&&d<=best;y++)for(let x=0;x<8;x++){const v=gAt(g,w,h,Hr,(116+40*x)/512,(116+40*y)/512);if(v<0){d=99;break;}if((v<th?1:0)!==MKBITS[y*8+x])d++;}
    if(d<best){best=d;rot=r;}}
  if(best>9)return null;
  return {q:[c[rot],c[(rot+1)%4],c[(rot+2)%4],c[(rot+3)%4]],d:best};}
/* refina os cantos: ajusta uma reta em cada lado do contorno e cruza as retas (precisão abaixo de 1 pixel) */
function refineCorners(q,ct){const L=[];
  for(let i=0;i<4;i++){const a=q[i],b=q[(i+1)%4],dx=b.x-a.x,dy=b.y-a.y,len=Math.hypot(dx,dy),ux=dx/len,uy=dy/len;
    let n=0,mx=0,my=0;const pts=[];for(const p of ct){const t=(p.x-a.x)*ux+(p.y-a.y)*uy,d=-(p.x-a.x)*uy+(p.y-a.y)*ux;if(t>len*.12&&t<len*.88&&Math.abs(d)<2.5){pts.push(p);mx+=p.x;my+=p.y;n++;}}
    if(n<6)return q;mx/=n;my/=n;let sxx=0,sxy=0,syy=0;for(const p of pts){const x=p.x-mx,y=p.y-my;sxx+=x*x;sxy+=x*y;syy+=y*y;}
    const th=.5*Math.atan2(2*sxy,sxx-syy);L.push([mx,my,Math.cos(th),Math.sin(th)]);}
  const out=[];for(let i=0;i<4;i++){const A=L[(i+3)%4],B=L[i];const den=A[2]*B[3]-A[3]*B[2];if(Math.abs(den)<1e-6)return q;
    const t=((B[0]-A[0])*B[3]-(B[1]-A[1])*B[2])/den;const x=A[0]+A[2]*t,y=A[1]+A[3]*t;if(Math.hypot(x-q[i].x,y-q[i].y)>4)return q;out.push({x,y});}
  return out;}
function poseFromCorners(q,w,h,f){
  const img=q.map(p=>[p.x-w/2,h/2-p.y]);const H=homog([[-1.5,1.5],[1.5,1.5],[1.5,-1.5],[-1.5,-1.5]],img);if(!H)return null;
  const col=j=>new THREE.Vector3(H[0][j]/f,H[1][j]/f,-H[2][j]);const h1=col(0),h2=col(1),h3=col(2);
  let l=2/(h1.length()+h2.length());if(h3.z*l>0)l=-l;
  const a=h1.multiplyScalar(l).normalize(),b=h2.multiplyScalar(l).normalize(),t=h3.multiplyScalar(l);
  const m=a.clone().add(b).normalize(),p=new THREE.Vector3().crossVectors(a,b).cross(m).normalize();
  const r1=m.clone().sub(p).normalize(),r2=m.clone().add(p).normalize();
  let R1=r1,R2=r2;if(r2.dot(a)>r1.dot(a)){R1=r2;R2=r1;}const R3=new THREE.Vector3().crossVectors(R1,R2);
  return new THREE.Matrix4().set(R1.x,R2.x,R3.x,t.x, R1.y,R2.y,R3.y,t.y, R1.z,R2.z,R3.z,t.z, 0,0,0,1).multiply(mAW).invert();}
function detectMarker(){
  const vw=video.videoWidth,vh=video.videoHeight;if(!vw||video.readyState<2)return null;
  const sc=480/Math.max(vw,vh),w=Math.round(vw*sc),h=Math.round(vh*sc);
  if(CAM.cv.width!==w||CAM.cv.height!==h){CAM.cv.width=w;CAM.cv.height=h;}
  CAM.ctx.drawImage(video,0,0,w,h);const img=CAM.ctx.getImageData(0,0,w,h);
  CV.grayscale(img,cvG);CV.adaptiveThreshold(cvG,cvT,3,6);
  const cont=CV.findContours(cvT,cvB);let found=null,bestD=99,bestP=0,fct=null;
  for(const ct of cont){if(ct.length<w*.1)continue;const p=CV.approxPolyDP(ct,ct.length*.05);
    if(p.length!==4||!CV.isContourConvex(p)||CV.minEdgeLength(p)<12)continue;
    const dx1=p[1].x-p[0].x,dy1=p[1].y-p[0].y,dx2=p[2].x-p[0].x,dy2=p[2].y-p[0].y;if(dx1*dy2-dy1*dx2<0){const s=p[1];p[1]=p[3];p[3]=s;}
    const r=readMarker(cvG.data,w,h,p);if(!r)continue;const pr=CV.perimeter(p);
    if(r.d<bestD||(r.d===bestD&&pr>bestP)){found=r.q;bestD=r.d;bestP=pr;fct=ct;}}
  if(!found)return null;found=refineCorners(found,fct);
  const M=poseFromCorners(found,w,h,CAM.fr*Math.max(w,h));if(!M)return null;
  const p=new THREE.Vector3(),q=new THREE.Quaternion(),s=new THREE.Vector3();M.decompose(p,q,s);if(p.y<.1||!isFinite(p.x))return null;
  CAM.tp.copy(p);CAM.tq.copy(q);CAM.last=found;return true;}
function camFov(){if(!CAM.on||!video.videoWidth)return;const vw=video.videoWidth,vh=video.videoHeight,s=Math.max(innerWidth/vw,innerHeight/vh);
  camera.fov=2*Math.atan(innerHeight/2/(CAM.fr*Math.max(vw,vh)*s))*180/PI;camera.updateProjectionMatrix();}
video.addEventListener('loadedmetadata',camFov);video.addEventListener('resize',camFov);
CAM.sp=new THREE.Vector3();CAM.sq=new THREE.Quaternion();CAM.uYaw=0;CAM.uScale=1;
const qUser=new THREE.Quaternion(),yAx=new THREE.Vector3(0,1,0);
function camStep(){if(!CAM.on)return;
  if(detectMarker()){CAM.seen=performance.now();CAM.found++;
    if(!CAM.has||performance.now()-CAM.lastOk>500){CAM.sp.copy(CAM.tp);CAM.sq.copy(CAM.tq);CAM.has=true;}
    CAM.lastOk=performance.now();}
  /* suavização: parado fica firme, movimento rápido acompanha */
  const dp=CAM.sp.distanceTo(CAM.tp)/Math.max(1,CAM.tp.length()*.15),da=CAM.sq.angleTo(CAM.tq);
  const k=Math.min(.85,Math.max(.07,dp/.5,da/.2));
  CAM.sp.lerp(CAM.tp,k);CAM.sq.slerp(CAM.tq,k);
  /* gestos: girar e dar zoom no modelo = mover a câmera virtual em volta do marcador */
  qUser.setFromAxisAngle(yAx,-CAM.uYaw);
  camera.position.copy(CAM.sp).multiplyScalar(1/CAM.uScale).applyQuaternion(qUser);
  camera.quaternion.copy(qUser).multiply(CAM.sq);camera.updateMatrixWorld();}
const gPts=new Map();let gStart=null;
renderer.domElement.addEventListener('pointerdown',e=>{if(!CAM.on)return;gPts.set(e.pointerId,[e.clientX,e.clientY]);gStart=null;});
addEventListener('pointermove',e=>{if(!CAM.on||!gPts.has(e.pointerId))return;gPts.set(e.pointerId,[e.clientX,e.clientY]);
  const P=[...gPts.values()];
  if(!gStart)gStart={yaw:CAM.uYaw,sc:CAM.uScale,p:P.map(p=>p.slice()),d:P.length>1?Math.hypot(P[0][0]-P[1][0],P[0][1]-P[1][1]):0,n:P.length};
  if(P.length!==gStart.n){gStart=null;return;}
  if(P.length===1)CAM.uYaw=gStart.yaw+(P[0][0]-gStart.p[0][0])*.012;
  else if(gStart.d>10)CAM.uScale=Math.max(.4,Math.min(3,gStart.sc*Math.hypot(P[0][0]-P[1][0],P[0][1]-P[1][1])/gStart.d));});
document.addEventListener('gesturestart',e=>e.preventDefault());
const gEnd=e=>{gPts.delete(e.pointerId);gStart=null;};addEventListener('pointerup',gEnd);addEventListener('pointercancel',gEnd);
/* abre a câmera com prazo: se o celular não responder, avisa em vez de ficar carregando para sempre */
const withT=(p,ms)=>Promise.race([p,new Promise((_,r)=>setTimeout(()=>r(new Error('timeout')),ms))]);
async function camOpen(){
  if(!navigator.mediaDevices||!navigator.mediaDevices.getUserMedia)return 'nosupport';
  try{if(video.srcObject){video.srcObject.getTracks().forEach(t=>t.stop());video.srcObject=null;}
    let st;try{st=await withT(navigator.mediaDevices.getUserMedia({video:{facingMode:{ideal:'environment'},width:{ideal:1280},height:{ideal:720}},audio:false}),15000);}
    catch(e){if(e&&e.name==='OverconstrainedError')st=await withT(navigator.mediaDevices.getUserMedia({video:true,audio:false}),15000);else throw e;}
    video.muted=true;video.setAttribute('playsinline','');video.setAttribute('muted','');video.srcObject=st;video.style.display='block';
    try{await withT(video.play(),4000);}catch(e){}
    await withT(new Promise(r=>{if(video.readyState>=1)r();else video.addEventListener('loadedmetadata',()=>r(),{once:true});}),6000);
    return 'ok';}
  catch(e){video.style.display='none';return e&&(e.name==='NotAllowedError'||e.name==='SecurityError')?'denied':e&&e.message==='timeout'?'timeout':e&&(e.name==='NotReadableError'||e.name==='AbortError')?'busy':'error';}}
const CAMERR={denied:'O celular não deu permissão para a câmera. No iPhone: Ajustes › Apps › Safari › Câmera › Permitir (ou toque em "aA" na barra do endereço › Ajustes do Site › Câmera). Depois recarregue a página.',
  timeout:'A câmera não respondeu. Feche os apps que podem estar usando a câmera (WhatsApp, chamadas de vídeo, Instagram), recarregue a página e tente de novo.',
  busy:'A câmera está ocupada por outro app. Feche chamadas de vídeo e apps de câmera e tente de novo.',
  nosupport:'Este navegador não libera a câmera. Abra o link direto no Safari (iPhone) ou no Chrome (Android), não por dentro do WhatsApp ou Instagram.',
  error:'Não consegui abrir a câmera. Recarregue a página e tente de novo.'};


/* ---------- utilidades ---------- */
const mat=(c,o={})=>new THREE.MeshStandardMaterial(Object.assign({color:c,roughness:.6,metalness:.1},o));
function box(w,h,d,c,o){return new THREE.Mesh(new THREE.BoxGeometry(w,h,d),mat(c,o));}
function cyl(r,h,c,o,seg=24){return new THREE.Mesh(new THREE.CylinderGeometry(r,r,h,seg),mat(c,o));}
function at(m,x,y,z){m.position.set(x,y,z);return m;}
function canvasTex(w,h,draw){const c=document.createElement('canvas');c.width=w;c.height=h;draw(c.getContext('2d'),w,h);const t=new THREE.CanvasTexture(c);t.encoding=THREE.sRGBEncoding;t.anisotropy=4;return t;}
function label(text,o={}){const fs=44,pad=18;const g0=document.createElement('canvas').getContext('2d');g0.font=`700 ${fs}px "Chakra Petch", Arial, sans-serif`;
  const tw=Math.ceil(g0.measureText(text).width)+pad*2,th=fs+pad;
  const tex=canvasTex(tw,th,(g,w,h)=>{g.fillStyle=o.bg||'rgba(20,26,34,.92)';const r=h/2;g.beginPath();g.moveTo(r,0);g.arcTo(w,0,w,h,r);g.arcTo(w,h,0,h,r);g.arcTo(0,h,0,0,r);g.arcTo(0,0,w,0,r);g.fill();
    g.font=`700 ${fs}px "Chakra Petch", Arial, sans-serif`;g.fillStyle=o.fg||'#fff';g.textAlign='center';g.textBaseline='middle';g.fillText(text,w/2,h/2+2);});
  const s=new THREE.Sprite(new THREE.SpriteMaterial({map:tex,depthTest:false,transparent:true}));const sz=o.size||.2;s.scale.set(sz*tw/th,sz,1);s.renderOrder=10;return s;}
const glowTex=canvasTex(128,128,(g,w,h)=>{const r=g.createRadialGradient(64,64,0,64,64,64);r.addColorStop(0,'rgba(255,255,255,1)');r.addColorStop(.35,'rgba(255,255,255,.45)');r.addColorStop(1,'rgba(255,255,255,0)');g.fillStyle=r;g.fillRect(0,0,w,h);});
function wire(pts,color,r=.018){const curve=new THREE.CatmullRomCurve3(pts.map(p=>new THREE.Vector3(...p)));return new THREE.Mesh(new THREE.TubeGeometry(curve,40,r,8,false),mat(color,{roughness:.45}));}

/* ---------- mesa e marcador (modo sem câmera) ---------- */
const env=new THREE.Group();scene.add(env);
const wood=canvasTex(512,512,(g,w,h)=>{g.fillStyle='#4a3a2c';g.fillRect(0,0,w,h);for(let i=0;i<90;i++){g.strokeStyle=`rgba(${30+Math.random()*40},${20+Math.random()*25},10,.25)`;g.lineWidth=1+Math.random()*3;g.beginPath();const y=Math.random()*h;g.moveTo(0,y);g.bezierCurveTo(w*.3,y+Math.random()*20-10,w*.7,y+Math.random()*20-10,w,y+Math.random()*16-8);g.stroke();}});
wood.wrapS=wood.wrapT=THREE.RepeatWrapping;wood.repeat.set(2,2);
const table=new THREE.Mesh(new THREE.CircleGeometry(7,64),mat(0xffffff,{map:wood,roughness:.8}));table.rotation.x=-PI/2;table.position.y=-.005;env.add(table);
const markerTex=canvasTex(512,512,(g,w,h)=>{g.fillStyle='#fff';g.fillRect(0,0,w,h);g.fillStyle='#111';g.fillRect(0,0,w,h);g.fillStyle='#fff';g.fillRect(52,52,w-104,h-104);
  g.fillStyle='#111';for(let y=0;y<8;y++)for(let x=0;x<8;x++)if(MKBITS[y*8+x])g.fillRect(116+40*x-20,116+40*y-20,40,40);});
const markerPlane=new THREE.Mesh(new THREE.PlaneGeometry(3,3),new THREE.MeshStandardMaterial({map:markerTex,roughness:.9}));markerPlane.rotation.x=-PI/2;env.add(markerPlane);
const paper=new THREE.Mesh(new THREE.PlaneGeometry(3.6,4.4),mat(0xf4f2ec,{roughness:.95}));paper.rotation.x=-PI/2;paper.position.set(0,-.002,.25);env.add(paper);

/* ---------- peças de hardware ---------- */
function mkCPU(){const g=new THREE.Group();g.add(at(box(.44,.03,.44,0x2d6b3c),0,0,0));g.add(at(box(.34,.035,.34,0xc9cdd3,{metalness:.7,roughness:.3}),0,.03,0));
  const tri=new THREE.Mesh(new THREE.ShapeGeometry(new THREE.Shape([new THREE.Vector2(0,0),new THREE.Vector2(.08,0),new THREE.Vector2(0,.08)])),mat(0xe0b44a,{metalness:.8,roughness:.3,side:THREE.DoubleSide}));
  tri.rotation.x=-PI/2;tri.position.set(-.21,.017,.21);g.add(tri);return g;}
function mkCooler(){const g=new THREE.Group();g.add(at(cyl(.24,.06,0xb9bec6,{metalness:.7,roughness:.35}),0,0,0));
  const fins=new THREE.Group();for(let i=0;i<9;i++){fins.add(at(box(.5,.18,.012,0xd5d9de,{metalness:.6,roughness:.35}),0,.13,-.2+i*.05));}g.add(fins);
  const fan=at(cyl(.27,.08,0x1d2128),0,.27,0);g.add(fan);g.add(at(cyl(.08,.085,0x5a6270),0,.27,0));
  const ring=new THREE.Mesh(new THREE.TorusGeometry(.27,.015,8,40),mat(0x4aa8ff,{emissive:0x1d5c99}));ring.rotation.x=PI/2;ring.position.y=.31;g.add(ring);g.userData.fan=fan;return g;}
function mkRAM(lying,ddr5=true){const g=new THREE.Group();const pcb=box(.03,.3,1.15,0x1d6b45);g.add(pcb);
  for(let i=0;i<8;i++){g.add(at(box(.035,.12,.11,0x15181d),.012,.02,-.48+i*.137));}
  g.add(at(box(.031,.04,1.15,0xd9b34a,{metalness:.8,roughness:.3}),0,-.135,0));
  g.add(at(box(.032,.045,.025,0x10141a),0,-.135,ddr5?-.02:.12));
  const tex=label(ddr5?'DDR5':'DDR4',{size:.09,bg:'#0f3d28'});tex.position.set(.04,.1,.35);g.add(tex);
  if(lying){g.rotation.z=PI/2;}return g;}
function mkGPU(){const g=new THREE.Group();g.add(at(box(1.4,.12,.55,0x262b33),0,0,0));g.add(at(box(1.4,.02,.55,0x3a404b),0,.07,0));
  for(const x of [-.35,.35]){g.add(at(cyl(.21,.03,0x14171c),x,.09,0));g.add(at(cyl(.06,.035,0x6b7381),x,.1,0));}
  g.add(at(box(.9,.02,.04,0xd9b34a,{metalness:.8,roughness:.3}),-.1,-.07,.27));g.add(at(box(.1,.06,.1,0x10141a),.6,.09,-.2));return g;}
function mkSSD(){const g=new THREE.Group();g.add(box(.6,.025,.16,0x1a1d22));g.add(at(box(.38,.005,.12,0xe9eef5),.04,.016,0));g.add(at(box(.04,.02,.12,0xd9b34a,{metalness:.8}),-.3,0,0));return g;}
function mkPSU(){const g=new THREE.Group();g.add(at(box(.85,.5,.85,0x2b3038),0,.25,0));
  const grill=new THREE.Mesh(new THREE.RingGeometry(.1,.33,40),mat(0x14171c,{side:THREE.DoubleSide}));grill.rotation.x=-PI/2;grill.position.y=.505;g.add(grill);
  g.add(at(cyl(.1,.01,0x5a6270),0,.505,0));const t=label('650 W',{size:.09});t.position.set(0,.3,.44);g.add(t);return g;}
const RAMX={A1:.45,A2:.6,B1:.75,B2:.9};
function mkMobo(full){const g=new THREE.Group();
  g.add(at(box(2.4,.06,2.8,0x1f4d36),0,.03,0));
  const sock=at(box(.58,.05,.58,0x8b929c,{metalness:.5,roughness:.4}),-.3,.085,-.55);sock.userData.id='socket';g.add(sock);
  const st=new THREE.Mesh(new THREE.ShapeGeometry(new THREE.Shape([new THREE.Vector2(0,0),new THREE.Vector2(.07,0),new THREE.Vector2(0,.07)])),mat(0xe0b44a,{metalness:.8,side:THREE.DoubleSide}));
  st.rotation.x=-PI/2;st.position.set(-.58,.112,-.27);g.add(st);
  g.add(at(box(.95,.16,.16,0x7d858f,{metalness:.6,roughness:.35}),-.3,.14,-1.1));g.add(at(box(.16,.16,.8,0x7d858f,{metalness:.6,roughness:.35}),-.95,.14,-.55));
  for(const [k,x] of Object.entries(RAMX)){const s=at(box(.07,.07,1.2,(k==='A2'||k==='B2')?0x3d4654:0x15181d),x,.095,-.55);s.userData.id=k;g.add(s);
    g.add(at(box(.08,.08,.05,0xe9eef5),x,.1,-1.17));g.add(at(box(.08,.08,.05,0xe9eef5),x,.1,.07));}
  const x16=at(box(1.5,.06,.09,0x15181d),-.35,.09,.5);x16.userData.id='x16';g.add(x16);
  const x1=at(box(.45,.06,.09,0x15181d),-.85,.09,.88);x1.userData.id='x1';g.add(x1);
  const m2=at(box(.6,.03,.16,0x2a3a30),-.25,.075,.15);m2.userData.id='m2';g.add(m2);
  g.add(at(box(.5,.12,.5,0x5f6773,{metalness:.5}),.45,.12,.95));g.add(at(box(.16,.14,.55,0xe9eef5),1.1,.13,-.2));
  if(full){g.userData.labels={};for(const k of Object.keys(RAMX)){const l=label(k,{size:.13});l.position.set(RAMX[k],.32,-1.32);g.add(l);g.userData.labels[k]=l;}
    const lx=label('PCIe x16',{size:.11});lx.position.set(-.35,.25,.62);g.add(lx);const l1=label('x1',{size:.11});l1.position.set(-.85,.25,1.0);g.add(l1);}
  return g;}

/* ---------- peças de robótica ---------- */
const PIN={GND:[-1.35,-.72],'13':[-1.2,-.72],'12':[-1.05,-.72],'11':[-.9,-.72],'5V':[-1.2,.32]};
function mkArduino(){const g=new THREE.Group();
  const top=canvasTex(512,384,(c,w,h)=>{c.fillStyle='#1b6fa8';c.fillRect(0,0,w,h);c.fillStyle='rgba(255,255,255,.9)';c.font='700 46px "Chakra Petch", Arial';c.fillText('ARDUINO',150,230);c.font='600 30px Arial';c.fillText('UNO',152,270);
    c.strokeStyle='rgba(255,255,255,.35)';c.lineWidth=3;c.strokeRect(14,14,w-28,h-28);});
  const board=new THREE.Mesh(new THREE.BoxGeometry(1.6,.05,1.2),[mat(0x1b6fa8),mat(0x1b6fa8),new THREE.MeshStandardMaterial({map:top,roughness:.6}),mat(0x1b6fa8),mat(0x1b6fa8),mat(0x1b6fa8)]);
  board.position.y=.025;g.add(board);
  g.add(at(box(.3,.18,.3,0xb9bec6,{metalness:.8,roughness:.3}),-.72,.12,.25));g.add(at(box(.25,.18,.22,0x15181d),-.72,.12,-.15));
  g.add(at(box(.5,.06,.14,0x15181d),.4,.08,-.2));
  g.add(at(box(.9,.1,.08,0x15181d),-.2,.1,-.52));g.add(at(box(.55,.1,.08,0x15181d),-.3,.1,.52));
  return g;}
function mkPins(g,which){const out={};for(const k of which){const [x,z]=PIN[k];const p=at(box(.11,.12,.11,k==='GND'?0x2b2f36:0x15181d),x,.11,z);p.userData.id=k;g.add(p);
  const hole=at(box(.05,.01,.05,0xd9b34a,{metalness:.8}),x,.175,z);g.add(hole);
  const l=label(k,{size:.1});l.position.set(x,.33,z+(z<0?-.1:.1));g.add(l);out[k]=new THREE.Vector3(x,.17,z);}return out;}
function mkProto(){const g=new THREE.Group();
  const t=canvasTex(512,352,(c,w,h)=>{c.fillStyle='#f1efe9';c.fillRect(0,0,w,h);c.fillStyle='#d23b3b';c.fillRect(20,14,w-40,4);c.fillStyle='#2b62c9';c.fillRect(20,44,w-40,4);
    c.fillStyle='#d23b3b';c.fillRect(20,h-48,w-40,4);c.fillStyle='#2b62c9';c.fillRect(20,h-18,w-40,4);c.fillStyle='#cfccc4';c.fillRect(0,h/2-6,w,12);
    c.fillStyle='#3a3a3a';for(let x=0;x<30;x++){for(let y=0;y<5;y++){c.fillRect(26+x*16,80+y*16,6,6);c.fillRect(26+x*16,190+y*16,6,6);}c.fillRect(26+x*16,26,6,6);c.fillRect(26+x*16,h-36,6,6);}});
  const b=new THREE.Mesh(new THREE.BoxGeometry(1.5,.08,1.03),[mat(0xf1efe9),mat(0xf1efe9),new THREE.MeshStandardMaterial({map:t,roughness:.8}),mat(0xf1efe9),mat(0xf1efe9),mat(0xf1efe9)]);b.position.y=.04;g.add(b);return g;}
function mkLED(color,on=false){const g=new THREE.Group();const c=new THREE.Color(color);
  const lens=mat(color,{transparent:true,opacity:.85,roughness:.2,emissive:c.clone().multiplyScalar(.08)});
  g.add(at(new THREE.Mesh(new THREE.CylinderGeometry(.07,.075,.12,24),lens),0,.14,0));const dome=at(new THREE.Mesh(new THREE.SphereGeometry(.07,24,12,0,PI*2,0,PI/2),lens),0,.2,0);g.add(dome);
  g.add(at(cyl(.009,.14,0xc9cdd3,{metalness:.8}),-.025,.03,0));g.add(at(cyl(.009,.18,0xc9cdd3,{metalness:.8}),.025,.01,0));
  const halo=new THREE.Sprite(new THREE.SpriteMaterial({map:glowTex,color,transparent:true,depthWrite:false,blending:THREE.AdditiveBlending}));halo.scale.set(.6,.6,1);halo.position.y=.18;halo.visible=false;g.add(halo);
  g.userData.set=v=>{lens.emissive.copy(c).multiplyScalar(v?1.1:.08);halo.visible=!!v;};g.userData.set(on);g.userData.color=color;return g;}
function mkResistor(){const g=new THREE.Group();const body=cyl(.04,.26,0xd8c8a0);body.rotation.z=PI/2;body.position.y=.1;g.add(body);
  [[-.07,0xd23b3b],[-.03,0xd23b3b],[.01,0x7a4a24],[.08,0xd9b34a]].forEach(([x,c])=>{const b=cyl(.042,.018,c);b.rotation.z=PI/2;b.position.set(x,.1,0);g.add(b);});
  for(const s of [-1,1]){const l=cyl(.008,.14,0xc9cdd3,{metalness:.8});l.rotation.z=PI/2;l.position.set(s*.2,.1,0);g.add(l);}return g;}
function mkUSB(){const g=new THREE.Group();g.add(at(box(.3,.14,.2,0x8b929c,{metalness:.6}),0,.07,0));g.add(wire([[.15,.07,0],[.45,.06,.05],[.7,.05,-.15],[.95,.05,0]],0x2b2f36,.035));return g;}

/* ---------- guias ---------- */
const MEMBERS={ar:['Ana Roberta','#f5c518'],al:['Ana Luísa','#ff8ab3'],lu:['Luiza','#5ee0a8'],gi:['Giovanna','#7fb8ff']};
function av(id){const m=MEMBERS[id];const ini=m[0].split(' ').map(s=>s[0]).join('').slice(0,2);return `<div class="av" style="background:${m[1]}" aria-hidden="true">${ini}</div>`;}
function say(id,text,tag){const m=MEMBERS[id];return `<div class="say">${av(id)}<div><small>${m[0]}${tag?' · '+tag:''}</small><p>${text}</p></div></div>`;}

/* ---------- trilhas ---------- */
const ICON={hw:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="6" y="6" width="12" height="12" rx="1.5"/><rect x="9.5" y="9.5" width="5" height="5"/><path d="M9 2v3M15 2v3M9 19v3M15 19v3M2 9h3M2 15h3M19 9h3M19 15h3"/></svg>',
  rb:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="5" y="8" width="14" height="11" rx="3"/><circle cx="9.5" cy="13.5" r="1.4" fill="currentColor"/><circle cx="14.5" cy="13.5" r="1.4" fill="currentColor"/><path d="M12 8V4M10 4h4M3 12v3M21 12v3"/></svg>',
  el:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M13 2L5 14h6l-1 8 8-12h-6z"/></svg>',
  rd:'<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><rect x="9" y="2" width="6" height="5" rx="1"/><rect x="2" y="17" width="6" height="5" rx="1"/><rect x="16" y="17" width="6" height="5" rx="1"/><path d="M12 7v5M5 17v-5h14v5"/></svg>'};
const TRACKS=[
  {id:'hw',short:'Hardware',name:'Montagem de hardware',desc:'Do primeiro encaixe ao PC completo',c:'#f5c518',ready:3,
   ph:['Conhecendo as peças','O processador','Memória RAM','Armazenamento','Placa de vídeo','Energia','Montagem completa','O PC não liga','Upgrade','Desafio final']},
  {id:'rb',short:'Robótica',name:'Robótica com Arduino',desc:'Do LED piscando ao carrinho autônomo',c:'#4aa8ff',ready:3,
   ph:['Conhecendo o Arduino','Pisca LED','Semáforo','Botão','Buzzer','Sensor de luz','Sensor de distância','Servo motor','O circuito não funciona','Carrinho autônomo']},
  {id:'el',name:'Eletrônica básica',desc:'Corrente, resistores e circuitos',c:'#ff8a3d',ready:0,
   ph:['O circuito fechado','Protoboard','Resistor','Série e paralelo','Lei de Ohm','Multímetro','Capacitor','Transistor','Achar o curto','Lanterna']},
  {id:'rd',name:'Redes',desc:'Da rede de casa à rede da escola',c:'#b98cff',ready:0,
   ph:['As peças da rede','O cabo de rede','Rede de casa','Endereço IP','Wi-Fi','Switch','Caminho do dado','Sem internet','Rede segura','Rede da escola']}];
const ROMAN=['I','II','III','IV','V','VI','VII','VIII','IX','X'];

/* ---------- progresso salvo ---------- */
const KEY='desmontar2-progresso';let P={done:{}};
try{const s=localStorage.getItem(KEY);if(s)P=JSON.parse(s)||P;if(!P.done)P.done={};}catch(e){}
function save(){try{localStorage.setItem(KEY,JSON.stringify(P));}catch(e){}}
const isOpen=(t,i)=>i===0||!!P.done[t+(i)];

/* ---------- estrelas ---------- */
const starSVG=(on,cls='')=>`<svg class="${cls}" viewBox="0 0 24 24"><path fill="${on?'#f5c518':'rgba(255,255,255,.16)'}" d="M12 2l3 6.5 7 .8-5.2 4.8 1.5 7L12 17.6 5.7 21.1l1.5-7L2 9.3l7-.8z"/></svg>`;
const lockSVG='<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2.2"><rect x="5" y="11" width="14" height="10" rx="2"/><path d="M8 11V8a4 4 0 018 0v3"/></svg>';

/* ---------- mapa ---------- */
const ZZ=[0,-64,-96,-64,0,64,96,64,0,-64];
function drawMap(){let total=0;Object.values(P.done).forEach(v=>total+=v);$('#starTotal').textContent=total;
  const z=P.done.zero;
  let h=`<button class="zero" data-go="zero"><div class="ic">0</div><div><b>Fase 0 · Como a RA funciona</b><span>Marcador, escala e rastreamento. Comece por aqui!</span></div><div class="st">${z?[1,2,3].map(i=>starSVG(i<=z)).join(''):''}</div></button>`;
  for(const t of TRACKS){const done=t.ph.filter((_,i)=>P.done[t.id+(i+1)]).length;
    h+=`<section class="track ${t.ready?'':'soon'}" style="--c:${t.c}"><header><div class="tic">${ICON[t.id]}</div><div><b>${t.name}</b><span>${t.desc}</span></div><div class="prog">${t.ready?`${done}/${t.ph.length}`:'Em breve'}</div></header>`;
    if(!t.ready){h+=`<div class="soonrow">${t.ph.map((n,i)=>`<i>${ROMAN[i]} · ${n}</i>`).join('')}</div></section>`;continue;}
    h+='<div class="path">';
    t.ph.forEach((n,i)=>{const id=t.id+(i+1),ready=i<t.ready,st=P.done[id],open=ready&&isOpen(t.id,i);
      const cls=st?'done':open?'open':'';const inner=!ready||!open?lockSVG:st?'✓':ROMAN[i];
      h+=`<button class="node ${cls}" style="transform:translateX(${ZZ[i]}px)" ${open?`data-go="${id}"`:'disabled'} aria-label="Fase ${ROMAN[i]}: ${n}${ready?'':' (em breve)'}"><div class="b">${inner}</div><div class="ss">${st?[1,2,3].map(k=>starSVG(k<=st)).join(''):''}</div><div class="nm">${ROMAN[i]} · ${n}${ready?'':'<br><small>em breve</small>'}</div></button>`;});
    h+='</div></section>';}
  $('#tracks').innerHTML=h;
  $('#tracks').querySelectorAll('[data-go]').forEach(b=>b.onclick=()=>openPhase(b.dataset.go));}
$('#resetBtn').onclick=()=>{P={done:{}};save();drawMap();toast('Progresso apagado.');};

/* ---------- fases ---------- */
const NAMES={mobo:'a placa-mãe',cpu:'o processador',ram:'a memória RAM',gpu:'a placa de vídeo',ssd:'o SSD',psu:'a fonte',socket:'o soquete do processador',
  A1:'o slot A1',A2:'o slot A2',B1:'o slot B1',B2:'o slot B2',x16:'o slot PCIe x16',x1:'o slot PCIe x1',m2:'o slot M.2',cpuIn:'o processador',
  ard:'o Arduino',proto:'a protoboard',led:'o LED',res:'o resistor',jumper:'o fio jumper',usb:'o cabo USB','13':'o pino 13','12':'o pino 12','11':'o pino 11',GND:'o pino GND','5V':'o pino 5V'};
let bench=new THREE.Group();scene.add(bench);
const R={};/* referências da bancada atual */
function setPick(o,id){o.userData.id=id;return o;}
function addPart(o,id,x,y,z,ly=.45){at(o,x,y,z);setPick(o,id);bench.add(o);R[id]=o;o.userData.ly=ly;return o;}
function showLabel(id,text){const o=R[id];if(!o||o.userData.lab)return;const l=label(text,{size:.15});l.position.set(o.position.x,o.position.y+(o.userData.ly||.45),o.position.z);bench.add(l);o.userData.lab=l;}

const PH={
zero:{track:null,title:'Como a RA funciona',c:'#36d399',
  build(){const g=new THREE.Group();const cube=at(box(.7,.7,.7,0x36d399,{roughness:.35}),0,.6,0);g.add(cube);
    const ring=new THREE.Mesh(new THREE.TorusGeometry(.75,.03,8,64),mat(0xf5c518,{emissive:0x5a4400}));ring.rotation.x=PI/2;ring.position.y=.05;g.add(ring);
    bench.add(g);R.spin=cube;},
  steps:[
    {k:'info',g:'ar',say:'Oi! Antes das trilhas, vamos entender a ferramenta. <b>Realidade aumentada (RA)</b> desenha objetos virtuais por cima da imagem da câmera, como se estivessem na sua mesa.',task:'Para isso o celular precisa saber onde a mesa está. É aí que entra o marcador impresso.'},
    {k:'choose',g:'al',say:'Olhe o marcador: borda preta grossa e quadradinhos pretos e brancos.',task:'Por que o marcador é assim?',
     opts:[{t:'Para a câmera achar os 4 cantos e reconhecer o desenho',ok:1,fb:'A câmera procura o contorno quadrado e lê os quadradinhos, como um QR code. Com os 4 cantos, ela calcula de que ângulo você está olhando.'},
       {t:'Só para ficar bonito',fb:'O desenho não é decoração: cada quadradinho é uma informação que a câmera lê.'},
       {t:'Para a câmera focar melhor',fb:'O foco é automático. O que importa são os cantos e o contraste forte entre preto e branco.'}],
     hint:'Pense em como um QR code é lido.'},
    {k:'ar',g:'lu',say:'Agora na prática. Coloque o marcador impresso na mesa, ligue a RA e aponte a câmera para ele.',task:'Faça a câmera reconhecer o marcador.',hint:'A folha inteira precisa aparecer na tela, com boa luz e sem reflexo.'},
    {k:'choose',g:'gi',say:'O marcador impresso tem 14 cm de lado, e o jogo sabe disso.',task:'Para que o jogo precisa saber o tamanho do marcador?',
     opts:[{t:'Para desenhar os objetos no tamanho certo em cima da mesa',ok:1,fb:'Sabendo o tamanho real, o jogo calcula a distância até a mesa e mantém a escala certa.'},
       {t:'Para saber a cor da mesa',fb:'O tamanho não tem relação com a cor. Ele serve para medir distância e escala.'},
       {t:'Não precisa: o jogo adivinha',fb:'Sem uma medida conhecida, um objeto perto e pequeno parece igual a um longe e grande.'}],hint:'Um objeto perto e pequeno parece igual a um longe e grande.'},
    {k:'choose',g:'ar',say:'A RA refaz a conta da posição muitas vezes por segundo. Isso se chama <b>rastreamento</b>.',task:'Se você tampar o marcador com a mão, o que acontece?',
     opts:[{t:'O objeto some, porque a RA não sabe mais onde desenhar',ok:1,fb:'Sem ver o marcador, a RA perde a referência. Quando ele volta, o objeto reaparece no mesmo lugar.'},
       {t:'O objeto continua igual',fb:'O objeto não está de verdade na mesa: ele só existe na tela, recalculado a partir do marcador.'},
       {t:'O objeto cai da mesa',fb:'Não há física aqui: sem o marcador, a RA simplesmente não sabe onde desenhar.'}],hint:'O objeto não existe de verdade na mesa.'}],
  learned:['A RA desenha objetos virtuais sobre a imagem da câmera','O marcador dá os 4 cantos que a câmera usa como referência','O tamanho conhecido do marcador garante a escala','Sem ver o marcador, o rastreamento se perde']},

hw1:{track:'hw',n:1,title:'Conhecendo as peças',
  build(){const m=mkMobo(false);m.scale.setScalar(.5);addPart(m,'mobo',0,0,-.15,.3);
    addPart(mkCPU(),'cpu',-1.2,.02,-1.35,.3);addPart(mkRAM(true),'ram',1.2,.02,-1.2,.3);const gp=mkGPU();gp.rotation.y=PI/2;addPart(gp,'gpu',1.2,.07,1.15,.35);
    const sd=mkSSD();sd.rotation.y=PI/2;addPart(sd,'ssd',-1.25,.02,-.1,.25);addPart(mkPSU(),'psu',-1.15,0,1.3,.75);},
  steps:[
    ['mobo','a placa-mãe','ar','A placa-mãe é a peça grande onde tudo se conecta. Ela liga processador, memória, placa de vídeo e SSD.','É a maior placa, com vários encaixes.'],
    ['cpu','o processador','al','O processador (CPU) é o cérebro do PC: faz os cálculos. É pequeno, quadrado e tem um triângulo dourado num canto.','Procure a peça pequena e quadrada, com a tampa prateada.'],
    ['ram','a memória RAM','lu','A memória RAM guarda o que está aberto agora. Quando o PC desliga, ela se apaga.','É uma placa comprida e fina, com chips pretos enfileirados.'],
    ['gpu','a placa de vídeo','gi','A placa de vídeo (GPU) desenha as imagens na tela. Nos jogos, é a peça que mais trabalha.','Procure a peça com ventoinhas redondas.'],
    ['ssd','o SSD','ar','O SSD guarda seus arquivos de forma permanente, mesmo com o PC desligado. É bem mais rápido que um HD.','É uma plaquinha preta, comprida e fina, com uma etiqueta.'],
    ['psu','a fonte','al','A fonte transforma a energia da tomada na energia que as peças usam (12 V, 5 V e 3,3 V).','É a caixa com uma grade de ventilação.']].map(([id,n,g,fb,hint])=>(
    {k:'tap',g,say:'Toque na peça que eu pedir. Se errar, eu mostro qual é.',task:`Toque n${n.startsWith('a ')?'a':'o'} ${n.slice(2)}`,ok:id,fb,hint,after(){showLabel(id,n.slice(2)[0].toUpperCase()+n.slice(3));}})),
  learned:['Placa-mãe: liga todas as peças','Processador: faz os cálculos','Memória RAM: guarda o que está aberto','Placa de vídeo: desenha as imagens','SSD: guarda os arquivos','Fonte: alimenta tudo']},

hw2:{track:'hw',n:2,title:'O processador',
  build(){const m=mkMobo(false);addPart(m,'mobo',0,0,0,.3);R.socket=m.children.find(o=>o.userData.id==='socket');
    const c=mkCPU();c.visible=false;bench.add(c);R.cpuNew=c;},
  steps:[
    {k:'choose',g:'ar',say:'A placa-mãe da bancada tem o soquete <b>S5</b>. O soquete é o encaixe do processador.',task:'Qual processador serve nessa placa?',
     opts:[{t:'Processador com soquete S5',s:'Mesmo encaixe da placa',ok:1,fb:'Isso! O processador precisa ter o mesmo soquete da placa-mãe, senão os contatos não batem.'},
       {t:'Processador com soquete S4',s:'Modelo mais antigo',fb:'Os contatos do S4 ficam em outras posições. Ele não encaixa no S5, mesmo sendo parecido.'},
       {t:'Qualquer processador serve',fb:'Cada placa-mãe aceita só os processadores do seu soquete. Por isso essa é a primeira coisa a conferir.'}],hint:'Procure o processador com o mesmo nome do soquete.'},
    {k:'tap',g:'al',say:'Agora vamos colocar o processador no lugar certo da placa.',task:'Toque no soquete do processador',ok:'socket',glow:['socket'],
     fb:'Esse é o soquete. Ele fica perto dos dissipadores de metal, que esfriam a energia que chega ao processador.',hint:'É o quadrado prateado perto das peças de metal.',
     after(){const c=R.cpuNew;c.visible=true;c.position.set(-.3,1.1,-.55);c.rotation.y=PI/2;tween(c,{y:.5},.6);}},
    {k:'choose',g:'lu',say:'Repare no <b>triângulo dourado</b> num canto do processador. O soquete também tem um.',task:'Como encaixar o processador?',
     opts:[{t:'Alinhar o triângulo do processador com o do soquete e soltar sem força',ok:1,fb:'Isso! Com os triângulos alinhados, ele cai no lugar sozinho. Não precisa apertar.'},
       {t:'Girar até entrar, em qualquer posição',fb:'Na posição errada ele não encaixa, e forçar entorta os contatos. Um contato torto pode estragar a placa.'},
       {t:'Apertar com força para firmar',fb:'O processador não precisa de força: ele só apoia no soquete. Quem prende é a alavanca do soquete.'}],hint:'O triângulo serve de guia.',
     after(){const c=R.cpuNew;tween(c,{y:.13,ry:0},.7);setPick(c,'cpuIn');}},
    {k:'choose',g:'gi',say:'Entre o processador e o cooler vai a <b>pasta térmica</b>. Ela preenche os buracos microscópicos entre as duas peças.',task:'Quanto de pasta térmica usar?',
     opts:[{t:'Uma gota do tamanho de um grão de ervilha',ok:1,fb:'Isso! A pressão do cooler espalha a gota sozinha numa camada fina.'},
       {t:'Uma camada bem grossa, cobrindo tudo',fb:'Pasta demais vaza pelas bordas e atrapalha. O que esfria é a camada fina, não a quantidade.'},
       {t:'Não precisa de pasta',fb:'Sem pasta sobra ar entre as peças. O ar conduz mal o calor, e o processador esquenta demais.'}],hint:'Menos é mais.',
     after(){const d=at(new THREE.Mesh(new THREE.SphereGeometry(.05,16,8),mat(0xb8bcc2,{roughness:.3,metalness:.2})),0,.05,0);d.scale.y=.5;R.cpuNew.add(d);}},
    {k:'tap',g:'ar',say:'Por último, o cooler: ele tira o calor do processador e joga para fora.',task:'Toque no processador para colocar o cooler',ok:'cpuIn',
     fb:'Pronto! O cooler apertou a pasta e já está girando. Processador instalado.',hint:'Toque na peça que você acabou de encaixar.',
     after(){const k=mkCooler();k.position.set(-.3,1.3,-.55);bench.add(k);R.cooler=k;tween(k,{y:.24},.8);}}],
  learned:['O soquete do processador precisa ser igual ao da placa','O triângulo dourado mostra a posição certa','Processador não se força: ele cai no lugar','Pasta térmica: uma gota do tamanho de uma ervilha','O cooler tira o calor do processador']},

hw3:{track:'hw',n:3,title:'Memória RAM',
  build(){const m=mkMobo(true);addPart(m,'mobo',0,0,0,.3);m.children.forEach(o=>{if(o.userData.id)R[o.userData.id]=o;});
    const c=mkCPU();at(c,-.3,.13,-.55);m.add(c);const k=mkCooler();at(k,-.3,.24,-.55);m.add(k);R.cooler=k;R.placed={};},
  steps:[
    {k:'choose',g:'lu',say:'Esta placa-mãe só aceita memória <b>DDR5</b>. Cada geração tem um corte (chanfro) num lugar diferente dos contatos.',task:'Qual pente de memória usar?',
     opts:[{t:'Pente DDR5',ok:1,fb:'Isso! O corte do pente bate com o ressalto do slot, então ele encaixa.'},
       {t:'Pente DDR4',fb:'O corte do DDR4 fica em outra posição. Ele não entra no slot DDR5, e forçar quebra o slot.'},
       {t:'Os dois servem',fb:'Cada placa aceita só uma geração de memória. DDR4 e DDR5 não são trocáveis.'}],hint:'Confira o que a placa aceita.'},
    {k:'tap',g:'gi',say:'Você tem <b>2 pentes</b> e a placa tem 4 slots: A1, A2, B1 e B2. O manual da placa manda usar <b>um slot de cada canal</b> (A e B).',task:'Toque no slot do primeiro pente',ok:'A2',glow:['A1','A2','B1','B2'],
     wrong:{A1:'Com 2 pentes, o manual manda começar pelo A2, o slot de cor diferente. O A1 é usado quando há 4 pentes.',B1:'O B1 só é usado com 4 pentes. Com 2, os slots certos são o A2 e o B2.',B2:'Quase! O B2 é para o segundo pente. Comece pelo A2.'},
     fb:'Isso! Primeiro pente no A2.',hint:'Os slots indicados costumam ter outra cor.',after(){placeRAM('A2');}},
    {k:'tap',g:'ar',say:'Agora o segundo pente. Lembre: um pente em cada canal.',task:'Toque no slot do segundo pente',ok:'B2',glow:['A1','B1','B2'],
     wrong:{A1:'Assim os dois pentes ficam no mesmo canal (A) e não trabalham juntos.',B1:'Está no canal certo, mas o manual indica o B2, igual ao A2 no outro canal.',A2:'O A2 já tem um pente.'},
     fb:'Isso! Um pente no canal A e outro no canal B.',hint:'Escolha o slot do canal B com a mesma cor do A2.',after(){placeRAM('B2');}},
    {k:'choose',g:'al',say:'Os dois pentes estão no lugar.',task:'Por que colocar um pente em cada canal?',
     opts:[{t:'Os dois trabalham ao mesmo tempo, e a memória fica mais rápida',s:'Isso se chama dual channel',ok:1,fb:'Isso! Em dual channel, o processador lê os dois pentes ao mesmo tempo, quase dobrando a velocidade.'},
       {t:'Para esfriar melhor',fb:'A distância ajuda um pouco no calor, mas o motivo principal é a velocidade: os dois canais trabalham juntos.'},
       {t:'Não faz diferença',fb:'Faz diferença sim: no mesmo canal, os pentes se revezam em vez de trabalhar juntos.'}],hint:'Pense em duas estradas em vez de uma.'},
    {k:'choose',g:'lu',say:'Última conferência antes de ligar.',task:'Como saber se o pente encaixou direito?',
     opts:[{t:'As travas das pontas fecham sozinhas com um clique',ok:1,fb:'Isso! Se as travas não fecharem, o pente não está todo para dentro. É um dos motivos mais comuns de PC que não liga.'},
       {t:'Ele fica um pouco solto, e isso é normal',fb:'Pente solto é problema: o PC pode nem ligar. Ele precisa ficar firme, com as travas fechadas.'},
       {t:'Só ligando o PC para saber',fb:'Dá para conferir antes: as travas das pontas precisam estar fechadas.'}],hint:'Olhe as pontas do slot.'}],
  learned:['A placa aceita só uma geração de memória (DDR4 ou DDR5)','Com 2 pentes, usar os slots A2 e B2','Um pente em cada canal = dual channel, mais rápido','As travas fechadas mostram que o pente encaixou']},

rb1:{track:'rb',n:1,title:'Conhecendo o Arduino',
  build(){const a=mkArduino();addPart(a,'ard',-.9,0,-.2,.4);const p=mkProto();addPart(p,'proto',.95,0,-.3,.3);
    addPart(mkLED(0xff3b3b),'led',-.35,0,1.15,.45);addPart(mkResistor(),'res',.25,0,1.2,.35);
    const j=new THREE.Group();j.add(wire([[0,.03,0],[.15,.25,.05],[.45,.25,-.05],[.6,.03,0]],0x2fb36b,.02));addPart(j,'jumper',.75,0,1.2,.45);
    addPart(mkUSB(),'usb',-1.35,0,1.35,.35);},
  steps:[
    ['ard','o Arduino','ar','O Arduino é uma placa com um pequeno computador (microcontrolador). Ele roda o seu programa e liga e desliga os pinos.','É a placa azul.'],
    ['proto','a protoboard','al','A protoboard é a placa de montar circuitos sem solda. Os furos de cada coluna são ligados por dentro.','É a placa branca cheia de furinhos.'],
    ['led','o LED','lu','O LED é uma luzinha. Ele só acende num sentido: a perna maior é o positivo (+).','É a peça pequena e vermelha, com duas perninhas.'],
    ['res','o resistor','gi','O resistor segura a corrente. Sem ele, o LED recebe energia demais e queima.','É a pecinha bege com listras coloridas.'],
    ['jumper','o fio jumper','ar','O jumper é o fio que liga o Arduino à protoboard.','É o fio verde.'],
    ['usb','o cabo USB','al','O cabo USB leva o programa do computador para o Arduino e também dá energia a ele.','É o cabo cinza na beira da mesa.']].map(([id,n,g,fb,hint])=>(
    {k:'tap',g,say:'Toque na peça que eu pedir. Se errar, eu mostro qual é.',task:`Toque n${n.startsWith('a ')?'a':'o'} ${n.slice(2)}`,ok:id,fb,hint,after(){showLabel(id,n.slice(2)[0].toUpperCase()+n.slice(3));}})),
  learned:['Arduino: roda o programa e controla os pinos','Protoboard: monta circuitos sem solda','LED: só acende num sentido','Resistor: protege o LED','Jumper: liga as peças','USB: leva o programa e a energia']},

rb2:{track:'rb',n:2,title:'Pisca LED',
  build(){const a=mkArduino();addPart(a,'ard',-.9,0,-.2,.4);R.pins=mkPins(bench,['GND','13','12','5V']);bench.children.forEach(o=>{if(PIN[o.userData.id])R[o.userData.id]=o;});
    const p=mkProto();addPart(p,'proto',.95,0,-.3,.3);const l=mkLED(0xff3b3b);l.visible=false;at(l,.6,.08,-.45);bench.add(l);R.led=l;
    const r=mkResistor();r.visible=false;at(r,1.0,.04,-.45);bench.add(r);R.res=r;},
  steps:[
    {k:'choose',g:'ar',say:'Primeiro projeto de verdade: fazer um LED piscar. O LED tem uma perna maior que a outra.',task:'O que a perna maior indica?',
     opts:[{t:'É o positivo (+), que recebe o sinal do Arduino',ok:1,fb:'Isso! Perna maior no +. Ao contrário, o LED não acende.'},
       {t:'É o negativo (−)',fb:'É o contrário: a perna maior é o positivo. A menor vai para o negativo (GND).'},
       {t:'Tanto faz o lado',fb:'O LED é um diodo: a corrente só passa num sentido. Ao contrário, ele fica apagado.'}],hint:'Maior = mais (+).',
     after(){R.led.visible=true;R.led.position.y=.7;tween(R.led,{y:.08},.6);}},
    {k:'choose',g:'gi',say:'O pino do Arduino solta 5 V. É energia demais para o LED sozinho.',task:'Qual resistor colocar junto do LED?',
     opts:[{t:'220 Ω',s:'Ω (ohm) é a unidade de resistência',ok:1,fb:'Isso! 220 Ω segura a corrente na medida: o LED acende bem e não queima.'},
       {t:'Nenhum, ligar direto',fb:'Sem resistor passa corrente demais. O LED esquenta e queima em segundos.'},
       {t:'1.000.000 Ω (1 MΩ)',fb:'Esse segura corrente demais: quase nada passa, e o LED nem acende.'}],hint:'Nem zero, nem exagero.',
     after(){R.res.visible=true;R.res.position.y=.6;tween(R.res,{y:.04},.6);}},
    {k:'tap',g:'lu',say:'Agora o fio. O sinal sai de um pino e o caminho termina no <b>GND</b>, que é o negativo. O programa vai controlar o <b>pino 13</b>.',task:'Toque no pino 13 do Arduino',ok:'13',glow:['GND','13','12','5V'],
     wrong:{GND:'O GND é o negativo, o fim do caminho. O sinal que liga e desliga sai do pino 13.','5V':'O 5V fica sempre ligado. O LED acenderia, mas nunca piscaria, porque o programa não controla esse pino.','12':'Quase! O programa vai usar o pino 13, logo ao lado.'},
     fb:'Isso! Fio do pino 13 até o LED, e outro fio do LED até o GND. O circuito está fechado.',hint:'Os números estão escritos em cima de cada pino.',
     after(){const p=R.pins;bench.add(wire([[p['13'].x,p['13'].y,p['13'].z],[p['13'].x,.45,p['13'].z+.1],[.35,.4,-.5],[.58,.1,-.45]],0xd23b3b));
       bench.add(wire([[p.GND.x,p.GND.y,p.GND.z],[p.GND.x,.55,p.GND.z+.05],[1.1,.5,-.75],[1.22,.1,-.45]],0x2b2f36));}},
    {k:'code',g:'gi',say:'Hora de programar! Toque nos blocos para montar o programa. O Arduino repete o programa para sempre.',task:'Monte o programa que faz o LED piscar',
     palette:[{id:'on',t:'Ligar LED',c:'on'},{id:'off',t:'Desligar LED',c:'off'},{id:'w1',t:'Esperar 1 s',c:'wait'}],max:6,
     check(p){const s=p.join(',');if(s==='on,w1,off,w1'||s==='off,w1,on,w1')return [1,'O LED liga, espera, desliga, espera e começa de novo. Está piscando!'];
       if(!p.includes('on'))return [0,'O LED nunca liga. Coloque o bloco <b>Ligar LED</b>.'];
       if(!p.includes('off'))return [0,'O LED liga e nunca desliga, então ele fica aceso o tempo todo.'];
       if(!p.includes('w1'))return [0,'Sem esperar, o Arduino liga e desliga milhares de vezes por segundo. Seus olhos veem o LED sempre aceso.'];
       if(p.filter(x=>x==='w1').length<2)return [0,'Falta uma espera. Depois de ligar e depois de desligar, o LED precisa ficar um tempo parado, senão um dos estados passa rápido demais.'];
       return [0,'Quase! Tente a ordem: ligar, esperar, desligar, esperar.'];},
     hint:'Liga → espera → desliga → espera.',fb:'Seu primeiro programa funcionou!'}],
  learned:['A perna maior do LED é o positivo (+)','Resistor de 220 Ω protege o LED','O sinal sai de um pino e volta pelo GND','Sem "esperar", a troca é rápida demais para os olhos']},

rb3:{track:'rb',n:3,title:'Semáforo',
  build(){const a=mkArduino();addPart(a,'ard',-.9,0,-.2,.4);R.pins=mkPins(bench,['GND','13','12','11']);bench.children.forEach(o=>{if(PIN[o.userData.id])R[o.userData.id]=o;});
    const p=mkProto();addPart(p,'proto',.95,0,-.3,.3);
    const cols={r:[0xff3b3b,-.7,'13',0xd23b3b],y:[0xffc21a,-.4,'12',0xe0a800],g:[0x2fe07a,-.1,'11',0x1f9e55]};R.leds={};
    for(const [k,[c,z,pin,wc]] of Object.entries(cols)){const l=mkLED(c);at(l,.6,.08,z);bench.add(l);R.leds[k]=l;const r=mkResistor();at(r,1.0,.04,z);bench.add(r);
      const q=R.pins[pin];bench.add(wire([[q.x,q.y,q.z],[q.x,.4+(-z)*.15,q.z+.1],[.3,.35,z-.05],[.58,.1,z]],wc));}
    const q=R.pins.GND;bench.add(wire([[q.x,q.y,q.z],[q.x,.7,q.z+.05],[1.2,.6,-.9],[1.3,.1,-.8]],0x2b2f36));
    const post=new THREE.Group();post.add(at(cyl(.05,1.3,0x2b2f36),0,.65,0));post.add(at(box(.34,.9,.26,0x1a1d22),0,1.6,0));
    R.lamps={};[['r',1.88],['y',1.6],['g',1.32]].forEach(([k,y])=>{const lc=R.leds[k].userData.color;const m=new THREE.Mesh(new THREE.SphereGeometry(.1,20,12),mat(lc,{emissive:new THREE.Color(lc).multiplyScalar(.06)}));m.position.set(0,y,.12);post.add(m);R.lamps[k]=m;});
    post.position.set(1.5,0,.75);bench.add(post);},
  steps:[
    {k:'choose',g:'ar',say:'Agora 3 LEDs: vermelho, amarelo e verde. Vamos programar um semáforo de carros.',task:'Qual é a ordem das cores de um semáforo no Brasil?',
     opts:[{t:'Verde → amarelo → vermelho → verde de novo',ok:1,fb:'Isso! O amarelo avisa que vai fechar. Depois do vermelho, volta direto o verde.'},
       {t:'Verde → vermelho → amarelo',fb:'O amarelo vem antes do vermelho, para avisar os motoristas que o sinal vai fechar.'},
       {t:'Vermelho → amarelo → verde',fb:'Em alguns países é assim, mas no Brasil o vermelho vai direto para o verde.'}],hint:'O amarelo é um aviso.'},
    {k:'choose',g:'al',say:'Cada luz fica acesa por um tempo diferente.',task:'Qual luz fica acesa por menos tempo?',
     opts:[{t:'O amarelo',ok:1,fb:'Isso! O amarelo só avisa que vai fechar, por isso dura pouco.'},{t:'O verde',fb:'O verde precisa durar bastante para os carros passarem.'},{t:'O vermelho',fb:'O vermelho dura bastante para os pedestres e a outra rua passarem.'}],hint:'Qual delas é só um aviso?'},
    {k:'tap',g:'lu',say:'Cada LED está ligado num pino diferente. Os fios têm a mesma cor do LED.',task:'Siga o fio do LED vermelho e toque no pino dele',ok:'13',glow:['GND','13','12','11'],
     wrong:{'12':'O pino 12 é o fio amarelo. Siga o fio vermelho.','11':'O pino 11 é o fio verde. Siga o fio vermelho.',GND:'O GND é o caminho de volta, comum aos três LEDs.'},
     fb:'Isso! Vermelho no 13, amarelo no 12 e verde no 11. No programa, cada bloco liga um desses pinos.',hint:'Gire a bancada para ver melhor os fios.'},
    {k:'code',g:'gi',say:'Agora monte o programa. Quando uma luz acende, as outras apagam. O programa repete para sempre.',task:'Programe o semáforo',
     palette:[{id:'g',t:'Verde acende',c:'g'},{id:'y',t:'Amarelo acende',c:'y'},{id:'r',t:'Vermelho acende',c:'r'},{id:'w5',t:'Esperar 5 s',c:'wait'},{id:'w2',t:'Esperar 2 s',c:'wait'}],max:8,
     check(p){const pairs=[];for(let i=0;i<p.length;i++){if('gyr'.includes(p[i])){const w=p[i+1];if(w!=='w5'&&w!=='w2')return [0,'Toda luz precisa de um <b>Esperar</b> logo depois. Sem isso, ela troca rápido demais.'];pairs.push(p[i]+w);i++;}else return [0,'Cada <b>Esperar</b> precisa vir logo depois de uma luz.'];}
       const want=['gw5','yw2','rw5'];const cols=pairs.map(x=>x[0]).join('');
       if(pairs.length!==3||!['gyr','yrg','rgy'].includes(cols))return [0,'Confira as cores: use cada luz uma vez, na ordem verde → amarelo → vermelho.'];
       const rot=cols==='gyr'?0:cols==='yrg'?1:2;const ok=pairs.every((x,i)=>x===want[(i+rot)%3]);
       if(ok)return [1,'Verde por 5 s, amarelo por 2 s, vermelho por 5 s, e começa de novo. É um semáforo de verdade!'];
       if(pairs.find(x=>x[0]==='y')!=='yw2')return [0,'O amarelo está durando demais. Ele é só um aviso: use <b>Esperar 2 s</b>.'];
       return [0,'Verde e vermelho precisam de mais tempo, para os carros passarem: use <b>Esperar 5 s</b>.'];},
     hint:'Verde (5 s) → amarelo (2 s) → vermelho (5 s).',fb:'Semáforo funcionando!'},
    {k:'choose',g:'ar',say:'Um teste de manutenção, como na vida real.',task:'Se o fio do pino 12 se soltar, o que acontece?',
     opts:[{t:'O amarelo nunca acende, e o resto funciona',ok:1,fb:'Isso! Cada LED tem seu próprio pino e seu próprio caminho. Só o amarelo para.'},
       {t:'O semáforo inteiro apaga',fb:'Cada LED tem seu próprio pino. Só o caminho do amarelo foi interrompido.'},
       {t:'O vermelho começa a piscar',fb:'O pino 12 é só do amarelo. O vermelho continua no pino 13, sem mudança.'}],hint:'Qual cor está no pino 12?'}],
  learned:['Vários LEDs, cada um no seu pino','Ordem do semáforo: verde → amarelo → vermelho','O amarelo dura menos porque é um aviso','Seguir os fios ajuda a achar defeitos']}
};
function placeRAM(k){const s=mkRAM(false);s.position.set(RAMX[k],1.1,-.55);bench.add(s);tween(s,{y:.27},.6);R.placed[k]=1;}

/* ---------- animações simples ---------- */
const tweens=[];
function tween(o,to,dur){const fr={x:o.position.x,y:o.position.y,z:o.position.z,ry:o.rotation.y};tweens.push({o,fr,to,t:0,dur:reduceMotion?.01:dur});}
function stepTweens(dt){for(let i=tweens.length-1;i>=0;i--){const w=tweens[i];w.t=Math.min(1,w.t+dt/w.dur);const k=1-Math.pow(1-w.t,3);
  for(const a of ['x','y','z'])if(w.to[a]!=null)w.o.position[a]=w.fr[a]+(w.to[a]-w.fr[a])*k;if(w.to.ry!=null)w.o.rotation.y=w.fr.ry+(w.to.ry-w.fr.ry)*k;if(w.t>=1)tweens.splice(i,1);}}

/* ---------- estado da fase ---------- */
let G=null;
const panel=$('#panel');
function openPhase(id){const ph=PH[id];if(!ph)return;idleSim=null;
  bench.parent&&scene.remove(bench);bench=new THREE.Group();scene.add(bench);for(const k in R)delete R[k];tweens.length=0;
  ph.build();G={id,ph,step:0,err:0,hints:0,fb:null,locked:false,prog:[],sim:null,hintOn:false,wrongShown:{}};
  const tr=TRACKS.find(t=>t.id===ph.track);const col=tr?tr.c:ph.c;document.body.style.setProperty('--c',col);
  $('#hudTrack').textContent=tr?`${tr.short} · Fase ${ROMAN[ph.n-1]}`:'Fase 0';$('#hudTitle').textContent=ph.title;
  $('#map').style.display='none';$('#hud').style.display='flex';panel.style.display='block';$('#result').style.display='none';
  resetView();renderStep();}
function backToMap(){if(CAM.on)arOff();G=null;$('#map').style.display='block';$('#hud').style.display='none';panel.style.display='none';$('#result').style.display='none';drawMap();}
$('#backBtn').onclick=backToMap;
function resetView(){const mob=innerWidth<760;camera.position.set(0,mob?6.4:3.9,mob?6.4:4.6);controls.target.set(0,0,mob?.35:.25);controls.update();}

function dotsHud(){const n=G.ph.steps.length;$('#hudSteps').innerHTML=G.ph.steps.map((_,i)=>`<i class="${i<G.step?'done':i===G.step?'on':''}"></i>`).join('');}
function renderStep(){if(!G)return;dotsHud();const s=G.ph.steps[G.step];let h=say(s.g,s.say);
  if(G.hintOn&&s.hint)h+=say(s.g==='ar'?'lu':'ar',s.hint,'Dica');
  h+=`<div class="task">${s.task}</div>`;
  if(G.fb)h+=`<div class="fb ${G.fb[0]}"><b>${G.fb[0]==='good'?'Isso!':'Ops!'}</b>${G.fb[1]}</div>`;
  if(G.locked){h+=`<button class="cta" id="nextBtn">${G.step<G.ph.steps.length-1?'Continuar':'Concluir fase'}</button>`;}
  else if(s.k==='info')h+=`<button class="cta" id="nextBtn">Continuar</button>`;
  else if(s.k==='choose')h+=`<div class="opts">${s.opts.map((o,i)=>`<button class="opt ${G.wrongShown[i]?'bad':''}" data-o="${i}">${o.t}${o.s?`<small>${o.s}</small>`:''}</button>`).join('')}</div>`;
  else if(s.k==='tap')h+=`<p class="tip">${CAM.on?'Toque na peça na tela. Arraste com um dedo para girar.':'Toque na peça na bancada. Arraste para girar e use dois dedos para dar zoom.'}</p>`;
  else if(s.k==='ar')h+=CAM.on?`<p class="tip">Procurando o marcador… A folha inteira precisa aparecer na tela.</p>`:`<button class="cta" id="arGo">Ligar a RA</button><button class="ghost" id="arSkip">Estou sem o marcador agora</button>`;
  else if(s.k==='code'){const pal=s.palette;const byId=Object.fromEntries(pal.map(b=>[b.id,b]));
    h+=`<div class="palette">${pal.map(b=>`<button class="blk ${b.c}" data-b="${b.id}">+ ${b.t}</button>`).join('')}</div>`;
    h+=`<div class="code">${G.prog.length?G.prog.map((id,i)=>`<div class="ln"><em>${i+1}</em><button class="blk ${byId[id].c}" data-rm="${i}">${byId[id].t}<span class="x">×</span></button></div>`).join(''):'<div class="empty">Toque nos blocos acima para montar o programa.</div>'}</div>`;
    h+=`<p class="loop">↻ repete para sempre</p><div class="row"><button class="ghost" id="clr" ${G.sim?'disabled':''}>Limpar</button><button class="cta" id="run" ${G.prog.length&&!G.sim?'':'disabled'}>${G.sim?'Rodando…':'▶ Rodar'}</button></div>`;}
  panel.innerHTML=h;panel.scrollTop=0;
  const nb=$('#nextBtn');if(nb)nb.onclick=next;
  panel.querySelectorAll('[data-o]').forEach(b=>b.onclick=()=>choose(+b.dataset.o));
  const ag=$('#arGo');if(ag)ag.onclick=arOn;const sk=$('#arSkip');if(sk)sk.onclick=()=>{good('Sem problema! Sem o marcador o jogo funciona aqui na tela. Quando tiver a folha impressa, toque em <b>Ligar RA</b> no topo.');};
  panel.querySelectorAll('[data-b]').forEach(b=>b.onclick=()=>{if(G.sim||G.prog.length>=s.max)return;G.prog.push(b.dataset.b);G.fb=null;renderStep();});
  panel.querySelectorAll('[data-rm]').forEach(b=>b.onclick=()=>{if(G.sim)return;G.prog.splice(+b.dataset.rm,1);renderStep();});
  const cl=$('#clr');if(cl)cl.onclick=()=>{G.prog=[];G.fb=null;renderStep();};const rn=$('#run');if(rn)rn.onclick=runCode;
  setGlow(s.k==='tap'&&!G.locked?(s.glow||[]):[]);viewOffset(true);}
function good(t){G.fb=['good',t];G.locked=true;const s=G.ph.steps[G.step];if(s.after)s.after();renderStep();}
function bad(t){G.err++;G.fb=['bad',t];renderStep();}
function next(){if(G.step<G.ph.steps.length-1){G.step++;G.fb=null;G.locked=false;G.prog=[];G.hintOn=false;G.wrongShown={};renderStep();}else finish();}
function choose(i){const s=G.ph.steps[G.step];if(G.locked)return;const o=s.opts[i];if(o.ok)good(o.fb);else{G.wrongShown[i]=1;bad(o.fb);}}
function tapped(id){if(!G||G.locked)return;const s=G.ph.steps[G.step];if(s.k!=='tap')return;
  if(id===s.ok){good(s.fb);return;}
  const msg=(s.wrong&&s.wrong[id])||(NAMES[id]?`${NAMES[id].startsWith('a ')?'Essa':'Esse'} é ${NAMES[id]}. ${s.hint||''}`:'Aí não tem nada para tocar.');
  if(NAMES[id]&&G.ph.steps.some(x=>x.ok===id&&x.after))showLabel(id,NAMES[id].slice(2)[0].toUpperCase()+NAMES[id].slice(3));bad(msg);}
$('#hintBtn').onclick=()=>{if(!G)return;const s=G.ph.steps[G.step];if(!s.hint||G.locked){toast('Nesta etapa é só ler e continuar.');return;}if(!G.hintOn){G.hintOn=true;G.hints++;}renderStep();};

/* código: confere e simula no 3D */
function runCode(){const s=G.ph.steps[G.step];const [ok,msg]=s.check(G.prog);G.sim={prog:G.prog.slice(),t:0,ok,msg,dur:G.id==='rb3'?6.5:4.2};renderStep();}
function stepSim(dt){const m=G&&G.sim;if(!m)return;m.t+=dt;const p=m.prog;
  const scale=G.id==='rb3'?.45:.5;const seq=[];let tt=0;for(const b of p){if(b[0]==='w'){tt+=(+b.slice(1))*scale;}else seq.push([tt,b]);}const loop=Math.max(tt,.06);
  const now=m.t%loop;let state=null;const noWait=tt===0;
  if(G.id==='rb2'){let on=false;for(const [t0,b] of seq){if(t0<=now)on=b==='on';}
    if(noWait)on=p.includes('on');if(seq.length&&!seq.some(([t0])=>t0<=now))on=seq[seq.length-1][1]==='on';R.led.userData.set(on);}
  else{let cur=null;for(const [t0,b] of seq)if(t0<=now)cur=b;if(!cur&&seq.length)cur=seq[seq.length-1][1];if(noWait)cur=null;
    for(const k of ['r','y','g']){const on=noWait?p.includes(k):cur===k;R.leds[k].userData.set(on);const lc=new THREE.Color(R.leds[k].userData.color);R.lamps[k].material.emissive.copy(lc).multiplyScalar(on?1:.06);}}
  if(m.t>=m.dur){G.sim=null;if(m.ok){G.sim=null;good(m.msg);keepSim(m.prog);}else{lightsOff();bad(m.msg);}}}
let idleSim=null;function keepSim(p){idleSim={prog:p,t:0};}
function lightsOff(){if(R.led)R.led.userData.set(false);if(R.leds)for(const k in R.leds){R.leds[k].userData.set(false);const lc=new THREE.Color(R.leds[k].userData.color);R.lamps[k].material.emissive.copy(lc).multiplyScalar(.06);}}

/* ---------- fim da fase ---------- */
function finish(){const tot=G.err+G.hints;const st=tot===0?3:tot<=2?2:1;const id=G.id;P.done[id]=Math.max(P.done[id]||0,st);save();
  const ph=G.ph;const tr=TRACKS.find(t=>t.id===ph.track);let nextId=null;if(tr&&ph.n<tr.ready)nextId=tr.id+(ph.n+1);
  $('#rcard').innerHTML=`<div class="big">${[1,2,3].map(i=>starSVG(i<=st,'pop')).join('')}</div><h2>Fase concluída!</h2><p>${st===3?'Perfeito, sem erros!':st===2?`${tot} ${tot===1?'erro ou dica':'erros ou dicas'}. Refaça para ganhar 3 estrelas.`:'Você conseguiu! Refaça para ganhar mais estrelas.'}</p>
    <div class="learn"><b>O que você aprendeu</b><ul>${ph.learned.map(x=>`<li>${x}</li>`).join('')}</ul></div>
    ${nextId?`<button class="cta" id="rNext">Próxima fase: ${ROMAN[ph.n]} · ${tr.ph[ph.n]}</button>`:''}<button class="${nextId?'ghost':'cta'}" id="rMap">Voltar ao mapa</button><button class="ghost" id="rAgain">Refazer fase</button>`;
  $('#rcard').querySelectorAll('.big svg').forEach((s,i)=>s.style.animationDelay=(i*.15)+'s');
  $('#result').style.display='grid';const rn=$('#rNext');if(rn)rn.onclick=()=>openPhase(nextId);$('#rMap').onclick=backToMap;$('#rAgain').onclick=()=>openPhase(id);}

/* ---------- toque nas peças ---------- */
const ray=new THREE.Raycaster();let down=null;
renderer.domElement.addEventListener('pointerdown',e=>{down=[e.clientX,e.clientY,performance.now()];});
renderer.domElement.addEventListener('pointerup',e=>{if(!down||!G)return;const mv=Math.hypot(e.clientX-down[0],e.clientY-down[1]);const dt=performance.now()-down[2];down=null;if(mv>9||dt>600)return;
  if(CAM.on&&performance.now()-CAM.seen>500){toast('Aponte para o marcador para ver a bancada.');return;}
  const r=renderer.domElement.getBoundingClientRect();ray.setFromCamera({x:(e.clientX-r.left)/r.width*2-1,y:-(e.clientY-r.top)/r.height*2+1},camera);
  const hits=ray.intersectObjects(bench.children,true);for(const h of hits){let o=h.object;while(o&&!o.userData.id&&o!==bench)o=o.parent;if(o&&o.userData.id&&o.visible!==false){tapped(o.userData.id);return;}}});

/* brilho nas áreas de toque */
let glowing=[];
function setGlow(ids){glowing.forEach(m=>{if(m.material&&m.userData.e0!=null)m.material.emissive.setHex(m.userData.e0);});glowing=[];
  for(const id of ids){const o=R[id];if(!o||!o.material)continue;o.userData.e0=o.material.emissive.getHex();glowing.push(o);}}

/* ---------- RA (câmera + marcador) ---------- */
async function arOn(){const b=$('#arBtn');b.disabled=true;$('#arLabel').textContent='Abrindo…';const r=await camOpen();b.disabled=false;
  if(r!=='ok'){$('#arLabel').textContent='Ligar RA';toast(CAMERR[r],8000);return;}
  CAM.on=true;CAM.has=false;CAM.found=0;CAM.uYaw=0;CAM.uScale=1;controls.enabled=false;env.visible=false;scene.background=null;camera.clearViewOffset();vOff=null;camFov();
  b.classList.add('on');$('#arLabel').textContent='RA ligada';renderStep();}
function arOff(){if(video.srcObject){video.srcObject.getTracks().forEach(t=>t.stop());video.srcObject=null;}video.style.display='none';CAM.on=false;controls.enabled=true;env.visible=true;scene.background=BG;bench.visible=true;
  $('#arBtn').classList.remove('on');$('#arLabel').textContent='Ligar RA';$('#arMsg').style.display='none';camera.fov=45;camera.updateProjectionMatrix();resetView();if(G)renderStep();}
$('#arBtn').onclick=()=>CAM.on?arOff():arOn();

/* ---------- tela e laço ---------- */
let vOff=null;
function viewOffset(force){const W=innerWidth,H=innerHeight;let off=0;
  let offX=0;if(!CAM.on&&panel.style.display!=='none'){if(W<760){const top=panel.getBoundingClientRect().top;off=Math.max(0,Math.round((H-top)/2-24));}else offX=Math.round((panel.offsetWidth+16)/2);}
  const key=off+','+offX;if(key!==vOff||force){vOff=key;if(off||offX)camera.setViewOffset(W,H,offX,off,W,H);else camera.clearViewOffset();}}
let wasMob=innerWidth<760;
function resize(){renderer.setSize(innerWidth,innerHeight);camera.aspect=innerWidth/innerHeight;camera.updateProjectionMatrix();vOff=null;if(CAM.on)camFov();
  const mob=innerWidth<760;if(mob!==wasMob){wasMob=mob;if(!CAM.on)resetView();}}
addEventListener('resize',resize);resize();
function toast(t,ms=4500){const el=$('#toast');el.textContent=t;el.style.display='block';clearTimeout(toast.t);toast.t=setTimeout(()=>el.style.display='none',ms);}
const clock=new THREE.Clock();let fr=0;
function loop(){requestAnimationFrame(loop);const raw=Math.min(clock.getDelta(),.5),dt=Math.min(raw,.05),t=clock.elapsedTime;fr++;
  stepTweens(dt);
  if(CAM.on){camStep();const seen=performance.now()-CAM.seen<500;bench.visible=seen;const m=$('#arMsg');m.style.display=seen?'none':'block';m.textContent='Aponte a câmera para o marcador DesmontAR';
    if(G&&!G.locked&&G.ph.steps[G.step].k==='ar'&&CAM.found>0)good('A câmera achou os 4 cantos, leu os quadradinhos e calculou de onde você está olhando. Mova o celular em volta: o objeto fica preso à folha.');}
  else{controls.update();if(fr%20===0)viewOffset();}
  if(R.spin){R.spin.rotation.y+=dt*.8;R.spin.position.y=.6+Math.sin(t*2)*.06;}
  if(R.cooler&&R.cooler.userData.fan)R.cooler.userData.fan.rotation.y+=dt*9;
  const pulse=.35+.35*Math.sin(t*5);glowing.forEach(m=>m.material.emissive.setRGB(pulse*.96,pulse*.77,pulse*.1));
  if(G&&G.sim)stepSim(raw);else if(idleSim&&G){idleSim.t+=raw;G.sim={prog:idleSim.prog,t:idleSim.t,dur:1e9,ok:1};stepSim(0);G.sim=null;}
  renderer.render(scene,camera);}
drawMap();loop();
window.__d2={openPhase,PH,G:()=>G,tapped,R,camera,THREE};
})();
