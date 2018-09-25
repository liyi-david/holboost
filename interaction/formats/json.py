from interaction.formats.format import Format
from kernel.declaration import *
from kernel.term import *
from kernel.task import Task

from interaction.commands import *

import json


class JsonConvertError(Exception):
    pass


class JsonFormat(Format):

    @staticmethod
    def import_term (external_t):
        # external term should be described by json string
        if isinstance(external_t, str):
            json_item = json.loads(external_t)
        else:
            json_item = external_t

        def convert(t):
            try:
                if t['type'] == 'sort':
                    sort_map = { 'type' : TYPE, 'set' : SET, 'prop' : PROP }
                    if t['sort'] not in sort_map:
                        raise JsonConvertError('invalid sort name %s' % t['sort'])
                    return sort_map[t['sort']]
                elif t['type'] == 'app':
                    args = list(map(convert, t['args']))
                    return Apply(convert(t['func']), *args)
                elif t['type'] == 'case':
                    return Case()
                elif t['type'] == 'cast':
                    return Cast(convert(t['body']), convert(t['guaranteed_type']))
                elif t['type'] == 'const':
                    return Const(t['name'])
                elif t['type'] == 'evar':
                    # FIXME
                    print('warn: evar is not fully supported yet')
                    return Evar()
                elif t['type'] == 'construct':
                    return Construct(t['mutind_name'], t['ind_index'], t['constructor_index'])
                elif t['type'] == 'lambda':
                    return Lambda(t['arg_name'], convert(t['arg_type']), convert(t['body']))
                elif t['type'] == 'letin':
                    return LetIn(t['arg_name'], convert(t['arg_type']), convert(t['arg_body']), convert(t['body']))
                elif t['type'] == 'ind':
                    return Ind(t['mutind_name'], t['ind_index'])
                elif t['type'] == 'var':
                    return Var(t['name'])
                elif t['type'] == 'rel':
                    return Rel(t['index'])
                elif t['type'] == 'prod':
                    return Prod(t['arg_name'], convert(t['arg_type']), convert(t['body']))
                elif t['type'] == 'fix':
                    return Const('TBD')
                else:
                    raise JsonConvertError('unhandled json node %s' % json.dumps(t))
            except KeyError as err:
                raise JsonConvertError('json key error %s in %s' % (err, json.dumps(t)))

        return convert(json_item)

    @staticmethod
    def import_command(json_item):
        if json_item is None:
            return IdleCommand()
        elif json_item['name'] == "rewrite":
            return RewriteCommand(
                    list(
                        map(
                            lambda hintrec : RewriteCommand.RewriteHint(
                                JsonFormat.import_term(hintrec['type']),
                                JsonFormat.import_term(hintrec['lemma']),
                                hintrec['right2left']
                            ),
                            json_item['hints']
                        )
                    )
                )


    @staticmethod
    def import_constant(json_item):
        return Constant(
                json_item['constant_name'],
                JsonFormat.import_term(json_item['constant_type']),
                None if 'constant_body' not in json_item else JsonFormat.import_term(json_item['constant_body'])
                )

    @staticmethod
    def import_mutind(json_item):

        def import_constructor(json_item):
            return MutInductive.Constructor(
                    json_item['constructor_name'],
                    JsonFormat.import_term(json_item['constructor_type'])
                    )

        def import_ind(json_item):
            return MutInductive.Inductive(
                    json_item['ind_name'],
                    JsonFormat.import_term(json_item['arity']),
                    [ import_constructor(c) for c in json_item['constructors'] ]
                    )

        return MutInductive(
                json_item['mutind_name'],
                [ import_ind(ind) for ind in json_item['inds'] ]
                )


    @staticmethod
    def import_task(external_t):
        # external term should be described by json string
        if isinstance(external_t, str):
            json_item = json.loads(external_t)
        else:
            json_item = external_t

        task = Task(
                JsonFormat.import_term(json_item['goal']),
                constants={ c['constant_name'] : JsonFormat.import_constant(c) for c in json_item['constants'] },
                variables = { c['variable_name'] : Constant(c['variable_name'], JsonFormat.import_term(c['variable_type'])) for c in json_item['variables'] },
                mutinds={ c['mutind_name'] : JsonFormat.import_mutind(c) for c in json_item['mutinds'] },
                command=JsonFormat.import_command(json_item['command'])
                )

        task.command.task = task
        return task

    @staticmethod
    def export_term(term: 'Term', as_dict=False) -> str:

        def convert(term):
            if isinstance(term, Sort):
                return { "type": "sort", "sort": term.sort.value }
            elif isinstance(term, Rel):
                return { "type": "rel", "index": term.index }
            elif isinstance(term, Var):
                # Var must be translated before Const since it is
                # a subclass of Const
                return { "type": "var",  "name": term.name }
            elif isinstance(term, Const):
                return { "type": "const",  "name": term.name }
            elif isinstance(term, Ind):
                return {
                        "type": "ind",
                        "mutind_name": term.mutind_name,
                        "ind_index": term.ind_index
                        }
            elif isinstance(term, Construct):
                return {
                        "type": "construct",
                        "mutind_name": term.mutind_name,
                        "ind_index": term.ind_index,
                        "constructor_index": term.constructor_index
                        }
            # TODO Evar
            # TODO Cast, Case
            # TODO Fix, CoFix, Proj
            elif isinstance(term, Prod):
                return {
                        "type": "prod",
                        "arg_name": term.arg_name,
                        "arg_type": convert(term.arg_type),
                        "body": convert(term.body)
                        }
            elif isinstance(term, Lambda):
                return {
                        "type": "lambda",
                        "arg_name": term.arg_name,
                        "arg_type": convert(term.arg_type),
                        "body": convert(term.body)
                        }
            elif isinstance(term, LetIn):
                return {
                        "type": "letin",
                        "arg_name": term.arg_name,
                        "arg_type": convert(term.arg_type),
                        "arg_body": convert(term.arg_body),
                        "body": convert(term.body)
                        }
            elif isinstance(term, Apply):
                return {
                        "type": "app",
                        "func": convert(term.func),
                        "args": list(map(lambda arg: convert(arg), term.args))
                        }
            else:
                raise JsonConvertError('cannot convert term typed %s' % t['type'])

        if as_dict:
            return convert(term)
        else:
            return json.dumps(convert(term))
