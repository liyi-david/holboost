import kernel.session as session

def declare_variable(names: 'str', type: 'Term') -> 'Term':
    sess = session.Session.get()


def show(name: 'str | Term'):
    sess = session.Session.get()
    if isinstance(name, str):
        pass
