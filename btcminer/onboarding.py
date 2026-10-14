"""First-run terminal configuration; no implicit mining or node installation."""
import getpass
import os
import sys
from . import service
from .settings import load, save, validate, CONFIG
from .protocol import script_for_address
from .connections import endpoint, PoolConnection
from .platform_support import bitcoin_directory


def ask(prompt, default='', check=None, secret=False):
    while True:
        suffix = (' ['+str(default)+']') if default and not secret else ''
        value = (getpass.getpass if secret else input)(prompt+suffix+': ').strip() or default
        try:
            if check: check(value)
            return value
        except (ValueError, TypeError): print('Invalid value. Please try again.')


def choice(values):
    def check(value):
        if value not in values: raise ValueError('Invalid choice')
    return check


def wizard():
    if not sys.stdin.isatty():
        raise ValueError('Setup requires a terminal. Automation: use config set KEY=value with secrets in environment variables.')
    if service.status().get('running'):
        raise ValueError('Stop this installation before running setup; existing settings are unchanged.')
    c = load()
    print('\nBTC MINER setup — setup does not start mining.')
    c['connection'] = ask('Connection: core or pool', c['connection'], choice(('core','pool')))
    c['network'] = ask('Network: mainnet, testnet4, testnet, regtest', c['network'],
                       choice(('mainnet','testnet4','testnet','regtest')))
    if c['connection']=='core':
        c['address'] = ask('Your payout address', c['address'], lambda v: script_for_address(v,c['network']))
        c['rpc_host'] = ask('Core RPC host', c['rpc_host'],
                            lambda v: validate(dict(c,rpc_host=v)))
        c['rpc_datadir'] = ask('Core data folder', c['rpc_datadir'] or str(bitcoin_directory()))
        c['rpc_cookie'] = ask('Cookie path (blank for automatic)', c['rpc_cookie'])
        port = ask('RPC port (0 uses network default)', str(c['rpc_port']),
                   lambda v: validate(dict(c,rpc_port=int(v))))
        c['rpc_port']=int(port)
        c['rpc_user']=ask('RPC username (blank uses local cookie)',c['rpc_user'])
        if c['rpc_user']:
            print('Set '+c['rpc_password_env']+' in your environment before starting. It is never saved by setup.')
    else:
        c['pool']=ask('Stratum endpoint, including stratum+ssl:// or stratum+tcp://', c['pool'],
                      lambda v:endpoint(v,c['tls']))
        c['pool_user']=ask('Pool username or address.worker',c['pool_user'],
                           lambda v: None if v else (_ for _ in ()).throw(ValueError()))
        c['pool_password']=ask('Pool password (blank uses x; stored in private local settings)', 'x',secret=True)
        c['backup']=ask('Backup endpoint (blank for none)',c['backup'],lambda v:endpoint(v,c['tls']) if v else None)
    maximum=os.cpu_count() or 1
    c['workers']=int(ask('Maximum local workers (1..%d)'%maximum,str(min(c['workers'],maximum)),
                          lambda v:validate(dict(c,workers=int(v)))))
    c['resource_control']=ask('Enable automatic CPU/RAM safeguards? y/n','y',choice(('y','n')))=='y'
    c['resource_min_workers']=min(2,c['workers']);c['resource_max_workers']=c['workers'];c['resource_external_workers']=0
    if c['resource_control']:
        c['resource_cpu_target']=int(ask('Host CPU target percent (1..89)','75',
            lambda v:validate(dict(c,resource_cpu_target=int(v)))))
        c['resource_rss_mib']=int(ask('Miner RAM ceiling in MiB',str(c['resource_rss_mib']),
            lambda v:validate(dict(c,resource_rss_mib=int(v)))))
    c['pause_on_active']=0 if sys.platform.startswith('linux') else c['pause_on_active']
    print('THESIS2 order: '+c['thesis2_order']+'; arithmetic, pruning, and distribution safeguards are preserved.')
    print('Provider integration is optional: configure your own BTC_PROVIDER_URL and BTC_PROVIDER_SESSION before enabling it.')
    c=validate(c)
    if ask('Save these settings? y/n','y',choice(('y','n')))!='y':
        return {'message':'Cancelled; existing settings unchanged.'}
    save(c)
    if ask('Check connection now? y/n','y',choice(('y','n')))=='y':
        try:
            if c['connection']=='core':
                from .diagnostics import doctor
                result=doctor(c,connect=True)
                print('Core readiness:', 'ready' if result.get('core_ready') else 'not ready')
            else:
                import time
                connection=PoolConnection(c,lambda *a,**kw:None)
                connection.start()
                try:
                    deadline=time.monotonic()+c['connect_timeout']+2
                    while time.monotonic()<deadline and not connection.connected: time.sleep(.1)
                    print('Pool:', 'connected' if connection.connected else 'not ready; inspect endpoint, credentials and TLS')
                finally: connection.close()
        except Exception:
            # Transport and provider text can contain credentials supplied by peers.
            print('Connection check failed. Run doctor --connect for bounded Core diagnostics; review local connection settings.')
    return {'message':'Saved. Run ui to review, then press s to start; or run start explicitly.', 'path':str(CONFIG)}
