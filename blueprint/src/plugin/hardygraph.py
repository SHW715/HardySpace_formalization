r"""
Package hardygraph

Turns the single, flat leanblueprint dependency graph into a two-level one.

The blueprint includes the main proof roadmap and supporting library results.
Book references are independent of this distinction. This package separates
the graph into two levels:

* statements marked with ``\mainline`` form the *main line*;
* every other statement is *auxiliary* and is attached to the main-line
  statements that depend on it.

The graph page then shows the main line by default, and lets the reader drill
down into the sub-blueprint of a single main-line statement.

Macros
------
``\bookref{source}{ref}{locator}``
    Record where a statement comes from, e.g.
    ``\bookref{Garnett}{I.6.7}{Chapter I, Section 6, PDF page 36}``.
    ``ref`` is also used in the sub-blueprint breadcrumb.

``\mainline``
    Include a statement in the main proof roadmap, independently of its source.

``\supports{label, ...}``
    Attach an auxiliary statement to the given main-line statements even when
    the dependency graph does not put it there, and make the first of them its
    owner.  Only needed to override the automatic assignment.

Hiding the auxiliary layer must not drop dependencies, so the main-line graph
is the *contraction* of the full graph: it has an edge ``A -> B`` whenever B
depends on A through a chain of auxiliary statements.

Everything is exposed to the graph template through
``document.userdata['hardygraph']``, whose ``build()`` method returns the
rendering data.  ``build()`` runs at render time, so node colours reflect the
final formalization status.
"""
import json
from pathlib import Path

from plasTeX import Command
from plasTeX.Logging import getLogger
from plasTeX.PackageResource import PackageTemplateDir

from plastexdepgraph.Packages.depgraph import DepGraph, item_kind

log = getLogger()

PKG_DIR = Path(__file__).parent

# Roles a node can play in a graph; they drive both styling and the legend.
ROLE_MAIN = 'main'          # a main-line statement, in the main-line graph
ROLE_ROOT = 'root'          # the statement a sub-blueprint belongs to
ROLE_OWN = 'own'            # auxiliary statement owned by this sub-blueprint
ROLE_SHARED = 'shared'      # auxiliary statement owned by another one
ROLE_BOUNDARY = 'boundary'  # main-line statement this one rests on

GHOST_COLORS = {ROLE_SHARED: '#9aa0a6', ROLE_BOUNDARY: '#497da5'}


class bookref(Command):
    r"""\bookref{source}{ref}{locator}"""
    args = 'source ref locator'

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.setUserData('bookref', {
            'source': self.attributes['source'].textContent,
            'ref': self.attributes['ref'].textContent,
            'locator': self.attributes['locator'].textContent,
        })


class mainline(Command):
    r"""\mainline"""

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.setUserData('hg_mainline', True)


class supports(Command):
    r"""\supports{labels list}"""
    args = 'labels:list:nox'

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        doc = self.ownerDocument

        def resolve():
            labels_dict = doc.context.labels
            pinned = []
            for label in self.attributes['labels']:
                if label in labels_dict:
                    pinned.append(labels_dict[label])
                else:
                    log.error("hardygraph: \\supports label '%s' could not be "
                              "resolved", label)
            node.setUserData('hg_supports', pinned)

        doc.addPostParseCallbacks(10, resolve)


def _walk(seed, adjacency, keep, stop_at):
    """
    Walk backwards from ``seed`` along ``adjacency``.

    Nodes in ``stop_at`` are collected but not walked through; nodes in
    ``keep`` are collected and walked through.  Anything else is ignored.
    Returns the pair (collected stop_at nodes, collected keep nodes).
    """
    stopped, kept, seen = set(), set(), set()
    stack = list(seed)
    while stack:
        node = stack.pop()
        if node in seen:
            continue
        seen.add(node)
        if node in stop_at:
            stopped.add(node)
        elif node in keep:
            kept.add(node)
            stack.extend(adjacency.get(node, ()))
    return stopped, kept


class HardyGraph:
    """Computes the two-level graph and renders it to dot."""

    def __init__(self, document):
        self.document = document
        self._result = None

    # -- called from the template ------------------------------------------

    def build(self):
        if self._result is None:
            self._result = self._build()
        return self._result

    # -- graph structure ---------------------------------------------------

    def _full_graph(self):
        graphs = self.document.userdata.get('dep_graph', {}).get('graphs', {})
        return graphs.get(self.document)

    def _build(self):
        doc = self.document
        graph = self._full_graph()
        if graph is None:
            log.warning('hardygraph: no whole-document dependency graph found; '
                        'the main-line view is disabled.')
            return self._disabled()

        nodes = set(graph.nodes)
        stmt_deps = {n: set() for n in nodes}
        proof_deps = {n: set() for n in nodes}
        for source, target in graph.edges:
            if source in nodes and target in nodes:
                stmt_deps[target].add(source)
        for source, target in graph.proof_edges:
            if source in nodes and target in nodes:
                proof_deps[target].add(source)
        deps = {n: stmt_deps[n] | proof_deps[n] for n in nodes}

        main = {n for n in nodes if n.userdata.get('hg_mainline')}
        if not main:
            log.warning('hardygraph: no statement is marked with \\mainline, so '
                        'there is no main line to show.')
            return self._disabled()
        aux = nodes - main

        # Contracted main-line edges.  An edge is solid when some chain
        # reaching it starts in a proof, dashed when every chain starts in a
        # statement, matching what solid and dashed mean in the full graph.
        main_stmt_edges, main_proof_edges = set(), set()
        boundary = {}
        for node in main:
            from_proof, _ = _walk(proof_deps[node], deps, aux, main)
            from_stmt, _ = _walk(stmt_deps[node], deps, aux, main)
            from_proof.discard(node)
            from_stmt.discard(node)
            boundary[node] = from_proof | from_stmt
            main_proof_edges |= {(d, node) for d in from_proof}
            main_stmt_edges |= {(d, node) for d in from_stmt - from_proof}

        # Auxiliary statements each main-line statement needs.
        support = {}
        for node in main:
            _, support[node] = _walk(deps[node], deps, aux, main)

        consumers = {}
        for node, reached in support.items():
            for a in reached:
                consumers.setdefault(a, set()).add(node)
        for a in aux:
            for pinned in (a.userdata.get('hg_supports') or []):
                if pinned in main:
                    consumers.setdefault(a, set()).add(pinned)
                    support[pinned].add(a)

        # Depth in the contracted graph, used to give a shared auxiliary
        # statement the most upstream of its consumers as its owner.
        main_adjacency = {n: set() for n in main}
        for source, target in main_stmt_edges | main_proof_edges:
            main_adjacency[target].add(source)
        depth = {}
        for node in main:
            _, reached = _walk(main_adjacency[node], main_adjacency, main, set())
            depth[node] = len(reached)

        def rank(node):
            return (depth[node], node.id)

        owner = {}
        for a, cs in consumers.items():
            pinned = [p for p in (a.userdata.get('hg_supports') or []) if p in main]
            owner[a] = min(pinned or cs, key=rank)

        orphans = sorted(aux - set(consumers), key=lambda n: n.id)
        if orphans:
            log.warning('hardygraph: %d auxiliary statement(s) no main-line '
                        'statement depends on: %s', len(orphans),
                        ', '.join(n.id for n in orphans))

        # -- dot rendering --------------------------------------------------

        counts = {n.id: len(support[n]) for n in main}
        dots = {}

        dots['__main__'] = self._dot(
            main,
            {n.id: ROLE_MAIN for n in main},
            edges=main_stmt_edges,
            proof_edges=main_proof_edges,
            counts=counts,
        )
        dots['__all__'] = self._dot(
            nodes,
            {n.id: (ROLE_MAIN if n in main else ROLE_OWN) for n in nodes},
            edges=graph.edges,
            proof_edges=graph.proof_edges,
        )

        for node in main:
            members = {node} | support[node] | boundary[node]
            roles = {node.id: ROLE_ROOT}
            for a in support[node]:
                roles[a.id] = ROLE_OWN if owner[a] is node else ROLE_SHARED
            for b in boundary[node]:
                roles[b.id] = ROLE_BOUNDARY
            dots[node.id] = self._dot(members, roles, edges=graph.edges,
                                      proof_edges=graph.proof_edges)

        if orphans:
            members = set(orphans)
            for node in orphans:
                members |= deps[node]
            roles = {n.id: (ROLE_ROOT if n in set(orphans) else
                            (ROLE_BOUNDARY if n in main else ROLE_SHARED))
                     for n in members}
            dots['__unattached__'] = self._dot(members, roles, edges=graph.edges,
                                               proof_edges=graph.proof_edges)

        titles = {}
        for node in nodes:
            book = node.userdata.get('bookref')
            titles[node.id] = book['ref'] if book else node.id.split(':')[-1]

        return {
            'enabled': True,
            'dots_json': json.dumps(dots),
            'counts': counts,
            'titles': titles,
            'titles_json': json.dumps(titles),
            'owner': {a.id: owner[a].id for a in owner},
            'main_count': len(main),
            'total_count': len(nodes),
            'orphans': [{'id': n.id, 'title': titles[n.id]} for n in orphans],
        }

    def _disabled(self):
        return {'enabled': False, 'dots_json': '{}', 'counts': {}, 'titles': {},
                'titles_json': '{}', 'owner': {}, 'main_count': 0,
                'total_count': 0, 'orphans': []}

    def _dot(self, members, roles, edges, proof_edges, counts=None):
        """Render one graph to a dot string, styled by each node's role."""
        members = set(members)
        if not members:
            return 'digraph {}'

        graph = DepGraph()
        graph.document = self.document
        graph.nodes = members
        graph.edges = {e for e in edges if e[0] in members and e[1] in members}
        graph.proof_edges = {e for e in proof_edges
                             if e[0] in members and e[1] in members}

        shapes = self.document.userdata['dep_graph'].get(
            'shapes', {'definition': 'box'})
        dot = graph.to_dot(shapes).tred()

        for node in dot.nodes():
            node_id = str(node)
            role = roles.get(node_id, ROLE_MAIN)
            node.attr['class'] = 'hg-' + role
            if role in GHOST_COLORS:
                node.attr['style'] = 'dashed'
                node.attr['color'] = GHOST_COLORS[role]
                node.attr['fillcolor'] = ''
            elif role == ROLE_ROOT:
                node.attr['penwidth'] = 3.2
            count = (counts or {}).get(node_id)
            if count:
                node.attr['label'] = '%s\\n+%d' % (node.attr['label'], count)
        return dot.to_string()


def ProcessOptions(options, document):
    """This is called when the package is loaded."""
    document.addPackageResource(
        PackageTemplateDir(path=PKG_DIR / 'renderer_templates'))
    document.userdata['hardygraph'] = HardyGraph(document)

    def update_status_and_legend():
        data = document.userdata['dep_graph']
        graph = data.get('graphs', {}).get(document)
        if graph is not None:
            # leanblueprint tests only statement leanok flags for can_prove,
            # and ignores notready on proofs. Readiness here requires completed
            # prerequisites, as promised by the legend.
            def complete(node):
                status = node.userdata
                if item_kind(node) == 'definition':
                    return bool(status.get('leanok'))
                return bool(status.get('proved') or status.get('mathlibok'))

            for node in graph.nodes:
                ancestors = graph.ancestors(node) - {node}
                prerequisites_done = all(complete(n) for n in ancestors)
                node.userdata['fully_proved'] = complete(node) and prerequisites_done
                proof = node.userdata.get('proved_by')
                node.userdata['can_prove'] = bool(
                    proof is not None
                    and not proof.userdata.get('notready')
                    and not node.userdata.get('notready')
                    and prerequisites_done)

        # Generate labels from the same palette keys as the colorizers.
        # Upstream uses can_state for the proof fill and proved for the
        # statement border, which breaks custom palettes, and omits defined.
        colors = data['colors']
        data['legend'] = [
            ('Boxes', 'definitions'),
            ('Ellipses', 'theorems and lemmas'),
            (f"{colors['can_state'][1]} border",
             'the <em>statement</em> is ready to be formalized; prerequisite statements are formalized'),
            (f"{colors['not_ready'][1]} border",
             'the <em>statement</em> is not ready to be formalized; the blueprint needs more work'),
            (f"{colors['stated'][1]} border", 'the <em>statement</em> is formalized'),
            (f"{colors['defined'][1]} background", 'the <em>definition</em> is formalized'),
            (f"{colors['can_prove'][1]} background",
             'a definition is ready to be formalized, or a proof is ready with all prerequisites complete'),
            ('Unfilled background', 'no proof is marked complete or ready'),
            (f"{colors['proved'][1]} background",
             'the <em>proof</em> is formalized; some prerequisites remain incomplete'),
            (f"{colors['fully_proved'][1]} background",
             'the <em>proof</em> and all its ancestors are formalized'),
            (f"{colors['mathlib'][1]} border", 'this is in Mathlib'),
            ('+n', 'auxiliary statements hidden behind a main-line node'),
            ('Dashed grey', 'auxiliary statement shown for context; it belongs '
                            'to another sub-blueprint'),
            ('Dashed blue', 'main-line statement this sub-blueprint rests on'),
        ]

    document.addPostParseCallbacks(160, update_status_and_legend)
