import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

SPEC = importlib.util.spec_from_file_location('aristotle_monitor', Path(__file__).resolve().parents[1]/'scripts/monitor_aristotle_math.py')
monitor = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(monitor)


class MonitorTests(unittest.TestCase):
    def run_cycle(self, task, report, reviewed, latest=None, validation_result=None, cached_latest=None, latest_reviewed=None):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            from btcminer.mathrevision import FILES
            for name in FILES:
                path = root/name
                path.parent.mkdir(parents=True,exist_ok=True)
                path.write_text('# fixture\n')
            reviewed = dict(reviewed, implementation={name:monitor.sha(root/name) for name in FILES})
            monitor.save(root/'latest-validation.json', report)
            monitor.save(root/'reference/aristotle-core-primes/reviewed-sources.json', reviewed)
            if latest_reviewed is not None:
                latest_reviewed = dict(latest_reviewed, implementation=reviewed['implementation'])
                monitor.save(root/'reference/aristotle-rods-towers/reviewed-sources.json', latest_reviewed)
            if cached_latest is not None:
                monitor.save(root/'task-validations'/(latest['agent_task_id']+'.json'), cached_latest)
            def get_task(route):
                return dict(task, agent_task_id=monitor.TASK) if route.endswith(monitor.TASK) else latest
            with patch.object(monitor, 'ROOT', root), patch.object(monitor, 'OUT', root), \
                 patch.object(monitor, 'get', side_effect=get_task), \
                 patch.object(monitor, 'latest_project_task', return_value=latest or dict(task, agent_task_id=monitor.TASK)), \
                 patch.object(monitor, 'validate', return_value=validation_result or {'ok':False}) as validate:
                result = monitor.cycle()
                if latest and latest['status']=='COMPLETE' and cached_latest is None:
                    validate.assert_called_once_with(latest)
                else:
                    validate.assert_not_called()
                self.assertEqual(json.loads((root/'latest-validation.json').read_text()),report)
                return result

    def test_completed_unchanged_reviewed_revision_matches(self):
        report = {'ok':True, 'remote_updated_at':'one', 'sources':{'A.lean':'abc'}}
        state = self.run_cycle({'status':'COMPLETE', 'last_updated_at':'one'}, report, {'sources':report['sources']})
        self.assertTrue(state['validation_ok'])
        self.assertEqual(state['implementation_review'], 'matches reviewed sources')

    def test_new_in_progress_revision_never_inherits_old_success(self):
        report = {'ok':True, 'remote_updated_at':'one', 'sources':{'A.lean':'abc'}}
        state = self.run_cycle({'status':'IN_PROGRESS', 'last_updated_at':'two'}, report, {'sources':report['sources']})
        self.assertFalse(state['validation_ok'])
        self.assertEqual(state['implementation_review'], 'pending')

    def test_validated_but_unreviewed_math_is_not_marked_integrated(self):
        report = {'ok':True, 'remote_updated_at':'two', 'sources':{'A.lean':'new'}}
        state = self.run_cycle({'status':'COMPLETE', 'last_updated_at':'two'}, report, {'sources':{'A.lean':'old'}})
        self.assertTrue(state['validation_ok'])
        self.assertEqual(state['implementation_review'], 'pending')

    def test_new_project_run_does_not_inherit_original_validation(self):
        report = {'ok':True, 'remote_updated_at':'one', 'sources':{'A.lean':'abc'}}
        for status, expected in [('IN_PROGRESS','awaiting completion'),
                                 ('COMPLETE','pending validation and implementation review')]:
            latest = {'agent_task_id':'new-run', 'status':status, 'percent_complete':15, 'last_updated_at':'two'}
            result = self.run_cycle({'status':'COMPLETE','last_updated_at':'one'}, report,
                                    {'sources':report['sources']}, latest)
            self.assertTrue(result['validation_ok'])
            self.assertTrue(result['newer_project_run_detected'])
            self.assertFalse(result['latest_task_validation_ok'])
            self.assertEqual(result['latest_task_implementation_review'], expected)

    def test_completed_new_run_is_audited_then_waits_for_implementation_review(self):
        report = {'ok':True, 'remote_updated_at':'one', 'sources':{'A.lean':'abc'}}
        latest = {'agent_task_id':'new-run', 'status':'COMPLETE', 'last_updated_at':'two'}
        validated = {'ok':True, 'task_id':'new-run', 'remote_updated_at':'two', 'targets':monitor.LATEST_TARGETS}
        for cached in (None, validated):
            result=self.run_cycle({'status':'COMPLETE','last_updated_at':'one'},report,
                                  {'sources':report['sources']},latest,validated,cached)
            self.assertTrue(result['latest_task_validation_ok'])
            self.assertEqual(result['latest_task_implementation_review'],
                             'selected math validated; pending implementation review')
            self.assertEqual(result['latest_task_validation_scope'],monitor.LATEST_TARGETS)

    def test_latest_integration_requires_its_own_task_and_sources(self):
        report = {'ok':True, 'remote_updated_at':'one', 'sources':{'A.lean':'abc'}}
        latest = {'agent_task_id':'new-run', 'status':'COMPLETE', 'last_updated_at':'two'}
        validated = {'ok':True, 'task_id':'new-run', 'remote_updated_at':'two',
                     'targets':monitor.LATEST_TARGETS, 'sources':{'A.lean':'new'}}
        for task_id, sources, matches in [('new-run',validated['sources'],True),
                                         ('wrong-run',validated['sources'],False),
                                         ('new-run',report['sources'],False)]:
            state = self.run_cycle({'status':'COMPLETE','last_updated_at':'one'},report,
                {'sources':report['sources']},latest,validated,validated,
                {'task_id':task_id,'sources':sources})
            self.assertEqual(state['latest_task_implementation_review']=='matches reviewed sources',matches)

    def test_validator_refuses_unfinished_runs_and_unsafe_report_paths(self):
        with self.assertRaisesRegex(ValueError,'Only completed'):
            monitor.validate({'status':'IN_PROGRESS'})
        with self.assertRaisesRegex(ValueError,'Invalid task ID'):
            monitor.validation_path('../outside')

    def test_background_audit_queues_without_running_lean_inline(self):
        with tempfile.TemporaryDirectory() as directory:
            task={'agent_task_id':'new-task','status':'COMPLETE'}
            with patch.object(monitor,'OUT',Path(directory)), \
                 patch.object(monitor,'queue_validation') as queue, \
                 patch.object(monitor,'validate') as validate:
                self.assertEqual(monitor.audit_or_queue(task,True),{})
                queue.assert_called_once_with(task)
                validate.assert_not_called()

    def test_active_audit_prevents_duplicate_workers(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            monitor.save(root/'active-validation.json',{'pid':123,'identity':'started','task_id':'old'})
            with patch.object(monitor,'OUT',root), patch.object(monitor,'miner_is_running',return_value=False), patch.object(monitor,'process_identity',return_value='started'), \
                 patch.object(monitor.subprocess,'Popen') as spawn:
                self.assertEqual(monitor.queue_validation({'agent_task_id':'new'})['pid'],123)
                spawn.assert_not_called()

    def test_unreviewed_or_failed_validation_never_deploys(self):
        with patch.object(monitor,'reviewed_update_candidate',return_value=None), \
             patch.object(monitor.subprocess,'run') as run:
            for state in ({}, {'latest_task_validation_ok':True},
                          {'latest_task_implementation_review':'matches reviewed sources'}):
                self.assertFalse(monitor.deploy_reviewed(state)['applied'])
            run.assert_not_called()

    def test_reviewed_update_can_deploy_while_newer_research_runs(self):
        with patch.object(monitor,'reviewed_update_candidate',return_value='reviewed-task'), \
             patch.object(monitor.subprocess,'run') as run:
            run.return_value.returncode=0
            run.return_value.stdout='{"applied":true}'
            result=monitor.deploy_reviewed({'latest_task_id':'new-task','latest_task_validation_ok':False})
            self.assertTrue(result['applied'])
            self.assertEqual(run.call_args.args[0][-1],'reviewed-task')

    def test_reviewed_candidate_requires_current_proofs_and_implementation(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            from btcminer.mathrevision import FILES
            names=FILES
            for name in names:
                path=root/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_text('# math')
            manifest={'task_id':'reviewed','sources':{'proof':'hash'},
                      'implementation':{name:monitor.sha(root/name) for name in names}}
            monitor.save(root/'reference/aristotle-rods-towers/reviewed-sources.json',manifest)
            report={'task_id':'reviewed','task_status':'COMPLETE','ok':True,'targets':monitor.LATEST_TARGETS,
                    'remote_updated_at':'now','sources':manifest['sources']}
            with patch.object(monitor,'ROOT',root),patch.object(monitor,'OUT',root), \
                 patch.object(monitor,'get',return_value={'agent_task_id':'reviewed','status':'COMPLETE','last_updated_at':'now'}), \
                 patch.object(monitor,'queue_validation') as queue:
                path=monitor.validation_path('reviewed')
                monitor.save(path,report)
                self.assertEqual(monitor.reviewed_update_candidate(),'reviewed')
                queue.assert_not_called()
                monitor.save(path,dict(report,targets=monitor.TARGETS))
                self.assertIsNone(monitor.reviewed_update_candidate())
                queue.assert_called_once()
                monitor.save(path,dict(report,sources={'proof':'changed'}))
                self.assertIsNone(monitor.reviewed_update_candidate())
                monitor.save(path,report)
                (root/names[0]).write_text('# changed after review')
                self.assertIsNone(monitor.reviewed_update_candidate())

    def test_hourly_interval_and_mining_defers_proofs(self):
        self.assertEqual(monitor.CHECK_INTERVAL,3600)
        with tempfile.TemporaryDirectory() as directory:
            with patch.object(monitor,'OUT',Path(directory)), \
                 patch.object(monitor,'miner_is_running',return_value=True), \
                 patch.object(monitor.subprocess,'Popen') as spawn:
                result=monitor.queue_validation({'agent_task_id':'pending'})
                self.assertEqual(result['state'],'deferred while miner is running')
                spawn.assert_not_called()
                with self.assertRaisesRegex(RuntimeError,'deferred'):
                    monitor.run_lean(['lean'],timeout=10)
                spawn.assert_not_called()

    def test_starting_miner_interrupts_active_proof_worker(self):
        with patch.object(monitor,'miner_is_running',side_effect=[False,True]), \
             patch.object(monitor.subprocess,'Popen') as spawn:
            process=spawn.return_value
            process.poll.return_value=None
            with self.assertRaisesRegex(RuntimeError,'protect running miner'):
                monitor.run_lean(['lean'],timeout=10)
            process.terminate.assert_called_once()
            process.wait.assert_called_once_with(timeout=5)

    def test_failed_retry_reuses_matching_historical_success(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory)
            report={'lean_version':'pinned','dependency_manifest_sha256':'deps','sources':{'A':'same'}}
            good=dict(report,ok=True,revision='old-success',axioms=['propext'])
            monitor.save(root/'revisions/old/validation.json',good)
            monitor.save(root/'revisions/wrong/validation.json',dict(good,lean_version='other'))
            monitor.save(root/'revisions/unsafe/validation.json',dict(good,axioms=['sorryAx']))
            with patch.object(monitor,'OUT',root):
                self.assertEqual(monitor.cached_success(report,{'ok':False}),good)
                self.assertEqual(monitor.cached_success(dict(report,dependency_manifest_sha256='changed'),{}),{})

    def test_latest_task_discovery_checks_all_pages(self):
        pages = [{'agent_tasks':[{'agent_task_id':'old','created_at':'2026-01-01'}], 'pagination_key':'next'},
                 {'agent_tasks':[{'agent_task_id':'new','created_at':'2026-09-29'}]}]
        with patch.object(monitor,'get',side_effect=pages) as get:
            self.assertEqual(monitor.latest_project_task()['agent_task_id'],'new')
            self.assertEqual(get.call_args.args[1],{'pagination_key':'next'})

    def test_latest_task_discovery_rejects_repeated_cursor(self):
        with patch.object(monitor,'get',return_value={'agent_tasks':[], 'pagination_key':'same'}):
            with self.assertRaisesRegex(RuntimeError,'Repeated'):
                monitor.latest_project_task()
