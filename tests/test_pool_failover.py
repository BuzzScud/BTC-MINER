"""Real local TCP Stratum fault injection; no external pool or live miner control."""
import json,socket,sys,threading,time,unittest
from pathlib import Path
from btcminer.connections import PoolConnection
from btcminer.settings import DEFAULTS
class Pool:
 def __init__(self,port=0):
  self.sock=socket.socket();self.sock.setsockopt(socket.SOL_SOCKET,socket.SO_REUSEADDR,1);self.sock.bind(('127.0.0.1',port));self.sock.listen();self.sock.settimeout(.1)
  self.port=self.sock.getsockname()[1];self.stop=threading.Event();self.clients=[];self.methods=[];self.auths=0
  self.thread=threading.Thread(target=self.run,daemon=True);self.thread.start()
 def run(self):
  while not self.stop.is_set():
   try:c,_=self.sock.accept()
   except socket.timeout:continue
   except OSError:return
   self.clients.append(c);threading.Thread(target=self.client,args=(c,),daemon=True).start()
 def client(self,c):
  c.settimeout(.1);data=b''
  try:
   while not self.stop.is_set():
    try:b=c.recv(65536)
    except socket.timeout:continue
    if not b:return
    data+=b
    while b'\n' in data:
     line,data=data.split(b'\n',1);request=json.loads(line);self.methods.append(request['method'])
     result=[[], 'aabb',4] if request['method']=='mining.subscribe' else True
     c.sendall((json.dumps({'id':request['id'],'result':result,'error':None})+'\n').encode())
     if request['method']=='mining.authorize':self.auths+=1
  except OSError:pass
  finally:c.close()
 def close(self):
  self.stop.set();self.sock.close()
  for c in self.clients:
   try:c.shutdown(socket.SHUT_RDWR)
   except OSError:pass
  self.thread.join(timeout=2)
def wait_for(pred,seconds=5):
 end=time.monotonic()+seconds
 while time.monotonic()<end:
  if pred():return True
  time.sleep(.03)
 return False
class FailoverTests(unittest.TestCase):
 def test_primary_recovers_with_one_failure_threshold(self):self.exercise(1)
 def test_primary_recovers_with_default_failure_threshold(self):self.exercise(5)
 def exercise(self,threshold):
  backup=Pool();self.addCleanup(backup.close)
  with socket.socket() as free:free.bind(('127.0.0.1',0));primary_port=free.getsockname()[1]
  events=[]
  config=dict(DEFAULTS,pool=f'stratum+tcp://127.0.0.1:{primary_port}',backup=f'stratum+tcp://127.0.0.1:{backup.port}',pool_user='local-test',pool_password='fixture',retry_seconds=.05,primary_retry_seconds=.1,retries_before_backup=threshold,connect_timeout=.2)
  connection=PoolConnection(config,lambda kind,message,**kw:events.append(message));connection.start()
  def close():connection.close();connection.thread.join(timeout=3)
  self.addCleanup(close)
  self.assertTrue(wait_for(lambda:backup.auths>=1 and connection.connected),'Never reached backup')
  generation=connection.generation
  primary=Pool(primary_port);self.addCleanup(primary.close)
  self.assertTrue(wait_for(lambda:primary.auths>=1 and connection.connected and connection.label==config['pool']),events)
  self.assertGreater(connection.generation,generation)
  self.assertNotIn('mining.submit',primary.methods+backup.methods)
if __name__=='__main__':unittest.main(verbosity=2)
