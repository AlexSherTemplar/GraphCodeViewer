import os
import ast
import glob
import re
import json
import dash
import collections
from dash import html, dcc, Input, Output, State, ALL, callback_context, ClientsideFunction
import dash_cytoscape as cyto
import dash_bootstrap_components as dbc

# ==========================================
# 0. CONFIG & UTILS
# ==========================================

class ConfigLoader:
    DEFAULT_CONFIG = {
        "theme": {
            "background_gradient": "linear-gradient(135deg, #2b2b2b 0%, #1a1a1a 100%)",
            "sidebar_bg": "#1e1e1e",
            "sidebar_border": "#444",
            "text_main": "#ffffff",
            "text_muted": "#aaaaaa",
            "input_bg": "#2d2d2d",
            "input_border": "#555",
            "accent_color": "#0074D9",
            "edge_color": "#00BFFF",
            "node_bg_default": "#333",
            "code_bg": "#1e1e1e",
            "scrollbar_thumb": "#555",
            "scrollbar_track": "#1e1e1e"
        }
    }
    @staticmethod
    def load():
        if os.path.exists("config.json"):
            try:
                with open("config.json", "r", encoding="utf-8") as f:
                    cfg = json.load(f)
                    base = ConfigLoader.DEFAULT_CONFIG.copy()
                    base['theme'].update(cfg.get('theme', {}))
                    return base
            except: pass
        return ConfigLoader.DEFAULT_CONFIG

CFG = ConfigLoader.load()['theme']

def calculate_complexity(code_str):
    return len(re.findall(r'\b(if|for|while|case|catch|except|with)\b', code_str)) + 1

def count_loc(code_str):
    return len([line for line in code_str.splitlines() if line.strip()])

# ==========================================
# 1. ANALYZER BACKEND
# ==========================================

class PythonAnalyzer(ast.NodeVisitor):
    def __init__(self):
        self.elements = {}
        self.calls = []
        self.var_usages = []
        self.global_vars = set()
        self.current_scope = None
        self.current_file = None
        self.file_content = ""
        self.source_lines = []

    def parse_file(self, file_path):
        self.current_file = file_path
        file_id = os.path.basename(file_path)
        self.elements[file_id] = {'id': file_id, 'name': file_id, 'type': 'file', 'lang': 'python', 'code': ''}
        self.current_scope = [file_id]
        try:
            with open(file_path, "r", encoding="utf-8", errors='ignore') as f:
                self.file_content = f.read()
                # Сохраняем код файла для отображения
                self.elements[file_id]['code'] = self.file_content
                self.source_lines = self.file_content.splitlines()
                tree = ast.parse(self.file_content)
                self.visit(tree)
        except: pass

    def _get_code(self, node):
        try:
            code_seg = ast.get_source_segment(self.file_content, node)
            if not code_seg: return ""
            start = node.lineno - 2
            comments = []
            while start >= 0:
                line = self.source_lines[start].strip()
                if line.startswith('#'): comments.insert(0, self.source_lines[start])
                elif not line: pass
                else: break
                start -= 1
            return "\n".join(comments) + "\n" + code_seg if comments else code_seg
        except: return ""

    def visit_ClassDef(self, node):
        class_id = f"{self.current_scope[-1]}::{node.name}"
        self.elements[class_id] = {
            'id': class_id, 'name': node.name, 'type': 'class', 'lang': 'python',
            'parent': self.current_scope[-1], 'code': self._get_code(node),
            'complexity': 0, 'loc': count_loc(self._get_code(node))
        }
        self.current_scope.append(class_id)
        self.generic_visit(node)
        self.current_scope.pop()

    def visit_FunctionDef(self, node):
        func_id = f"{self.current_scope[-1]}::{node.name}"
        code = self._get_code(node)
        f_type = 'dunder' if node.name.startswith("__") else 'function'
        self.elements[func_id] = {
            'id': func_id, 'name': node.name, 'type': f_type, 'lang': 'python',
            'parent': self.current_scope[-1], 'code': code,
            'complexity': calculate_complexity(code), 'loc': count_loc(code)
        }
        self.current_scope.append(func_id)
        self.generic_visit(node)
        self.current_scope.pop()

        for subnode in ast.walk(node):
            if isinstance(subnode, ast.Name) and isinstance(subnode.ctx, ast.Load):
                if subnode.id in self.global_vars:
                    self.var_usages.append((func_id, subnode.id))

    def visit_Assign(self, node):
        if len(self.current_scope) == 1:
            for target in node.targets:
                if isinstance(target, ast.Name): self._add_var(target.id, node)
        self.generic_visit(node)

    def _add_var(self, name, node):
        self.global_vars.add(name)
        var_id = f"{self.current_scope[-1]}::{name}"
        self.elements[var_id] = {
            'id': var_id, 'name': name, 'type': 'variable', 'lang': 'python',
            'parent': self.current_scope[-1], 'code': self._get_code(node),
            'complexity': 0, 'loc': 1
        }

    def visit_Call(self, node):
        if len(self.current_scope) > 1:
            caller = self.current_scope[-1]
            callee = None
            if isinstance(node.func, ast.Name): callee = node.func.id
            elif isinstance(node.func, ast.Attribute): callee = node.func.attr
            if callee:
                snip = ast.get_source_segment(self.file_content, node) or f"{callee}(...)"
                self.calls.append((caller, callee, snip))
        self.generic_visit(node)

class CppAnalyzer:
    def __init__(self):
        self.elements = {}
        self.calls = []
        self.var_usages = []
        self.keywords = {'if', 'while', 'for', 'switch', 'return', 'else', 'printf', 'std', 'int', 'void', 'bool', 'string', 'class', 'struct', 'public', 'private'}
        self.current_file = None
        self.original_content = ""
        self.masked_content = ""
        self.found_vars = set()

    def remove_comments(self, text):
        def replacer(match): return re.sub(r'[^\n]', ' ', match.group(0))
        return re.sub(r'//.*?$|/\*.*?\*/', replacer, text, flags=re.DOTALL | re.MULTILINE)

    def parse_file(self, file_path):
        self.current_file = file_path
        file_id = os.path.basename(file_path)
        try:
            with open(file_path, "r", encoding="utf-8", errors='ignore') as f:
                self.original_content = f.read()
                # Сохраняем весь контент файла
                self.elements[file_id] = {'id': file_id, 'name': file_id, 'type': 'file', 'lang': 'cpp', 'code': self.original_content}

                self.masked_content = self.remove_comments(self.original_content)
                self.found_vars = set()
                self.parse_block(self.masked_content, file_id)
        except: pass

    def parse_block(self, content, parent_id):
        var_pattern = re.compile(r'^\s*(?:(?:extern|static|const|constexpr)\s+)*([\w:<>*&]+)\s+(\w+)\s*(?:=.*|\(.*?\))?;', re.MULTILINE)
        for match in var_pattern.finditer(content):
            v_name = match.group(2)
            if v_name not in self.keywords:
                self.found_vars.add(v_name)
                var_id = f"{parent_id}::{v_name}"
                ls = self.original_content.rfind('\n', 0, match.start()) + 1
                le = self.original_content.find('\n', match.end())
                code = self.original_content[ls:le].strip()
                self.elements[var_id] = {'id': var_id, 'name': v_name, 'type': 'variable', 'lang': 'cpp', 'parent': parent_id, 'code': code, 'complexity': 0, 'loc': 1}

        class_pattern = re.compile(r'\b(class|struct)\s+(\w+)\s*(?::[^\{]+)?\s*\{')
        for match in class_pattern.finditer(content):
            c_name = match.group(2)
            c_id = f"{parent_id}::{c_name}"
            body, end = self.extract_body(content, match.end() - 1)
            full_code = self.get_original(match.start(), end)
            self.elements[c_id] = {
                'id': c_id, 'name': c_name, 'type': 'class', 'lang': 'cpp',
                'parent': parent_id, 'code': full_code, 'complexity': 0, 'loc': count_loc(full_code)
            }
            self.parse_block(body, c_id)

        func_pattern = re.compile(r'([\w:<>*&]+\s+)?((?:\w+::)*\w+|operator\S+|~\w+)\s*\(([^;]*?)\)\s*(?:const|override|final|noexcept)?\s*(?::[^\{]+)?\s*\{')
        for match in func_pattern.finditer(content):
            f_name = match.group(2).strip()
            clean_name = f_name.split('::')[-1]
            if clean_name in self.keywords: continue

            body, end = self.extract_body(content, match.end() - 1)
            f_id = f"{parent_id}::{f_name}"
            f_type = 'entry_point' if clean_name == 'main' else ('dunder' if clean_name.startswith('~') else 'function')
            full_code = self.get_original(match.start(), end, relative_to_content=content).lstrip(';}\n\r')

            self.elements[f_id] = {
                'id': f_id, 'name': f_name, 'type': f_type, 'lang': 'cpp',
                'parent': parent_id, 'code': full_code,
                'complexity': calculate_complexity(full_code), 'loc': count_loc(full_code)
            }
            self.find_calls(body, f_id)

    def find_calls(self, body, caller_id):
        call_p = re.compile(r'(\b(?:\w+::)*\w+)\s*\(')
        for cm in call_p.finditer(body):
            callee = cm.group(1).split('::')[-1]
            if callee not in self.keywords:
                snip = f"{callee}(...)"
                self.calls.append((caller_id, callee, snip))

        call_p2 = re.compile(r'(?:[\w>\]\)]+)(\.|->)(\w+)\s*\(')
        for cm in call_p2.finditer(body):
            if cm.group(2) not in self.keywords:
                snip = f"...{cm.group(1)}{cm.group(2)}(...)"
                self.calls.append((caller_id, cm.group(2), snip))

        for v in self.found_vars:
            if re.search(r'\b' + re.escape(v) + r'\b', body):
                self.var_usages.append((caller_id, v))

    def extract_body(self, text, start):
        balance = 0; idx = start; length = len(text)
        while idx < length:
            if text[idx] == '{': balance += 1
            elif text[idx] == '}': balance -= 1
            idx += 1
            if balance == 0: return text[start+1:idx-1], idx
        return "", idx

    def get_original(self, start, end, relative_to_content=None):
        if relative_to_content: return relative_to_content[start:end]
        return self.original_content[start:end]

class ProjectManager:
    def analyze(self, path, allowed_langs):
        py, cpp = PythonAnalyzer(), CppAnalyzer()
        if os.path.isfile(path):
            if path.endswith('.py'): py.parse_file(path)
            else: cpp.parse_file(path)
        elif os.path.isdir(path):
            if 'python' in allowed_langs:
                for f in glob.glob(os.path.join(path, "**/*.py"), recursive=True): py.parse_file(f)
            if 'cpp' in allowed_langs:
                for ext in ['*.cpp', '*.c', '*.h', '*.hpp']:
                    for f in glob.glob(os.path.join(path, "**/" + ext), recursive=True): cpp.parse_file(f)

        all_elems = {**py.elements, **cpp.elements}
        all_calls = py.calls + cpp.calls
        all_vars = py.var_usages + cpp.var_usages
        elements = []

        for eid, data in all_elems.items():
            classes = f"{data['type'].replace('_', '-')} {data['lang']}-node"
            if data.get('complexity', 0) > 10: classes += " complex-code"

            search_txt = f"{data['name']} {data.get('code','')}".lower()

            el = {
                'data': {
                    'id': eid,
                    'label': data['name'],
                    'name': data['name'],
                    'code': data['code'],
                    'type': data['type'],
                    'lang': data['lang'],
                    'complexity': data.get('complexity', 0),
                    'loc': data.get('loc', 0),
                    'search_text': search_txt
                },
                'classes': classes
            }
            if 'parent' in data and data['parent'] in all_elems:
                el['data']['parent'] = data['parent']
            elements.append(el)

        added_edges = set()
        for src, dest_name, snip in all_calls:
            for tid, tdata in all_elems.items():
                if tdata['name'] == dest_name and tdata['type'] != 'variable':
                    if all_elems[src]['lang'] == tdata['lang']:
                        edge_id = f"{src}->{tid}"
                        if edge_id not in added_edges:
                            root_src = src.split('::')[0]
                            root_tgt = tid.split('::')[0]
                            is_cross = root_src != root_tgt
                            elements.append({'data': {'source': src, 'target': tid, 'snippet': snip}, 'classes': 'cross-file' if is_cross else 'internal'})
                            added_edges.add(edge_id)

        for fid, vname in all_vars:
            for tid, data in all_elems.items():
                if data['type'] == 'variable' and data['name'] == vname:
                    if all_elems[fid]['lang'] == data['lang']:
                        if os.path.basename(all_elems[fid]['id'].split('::')[0]) == os.path.basename(data['id'].split('::')[0]):
                            edge_id = f"{fid}->{tid}"
                            if eid not in added_edges:
                                elements.append({'data': {'source': fid, 'target': tid}, 'classes': 'var-usage'})
                                added_edges.add(eid)
        return elements

# ==========================================
# 2. UI & LAYOUT
# ==========================================

app = dash.Dash(__name__, external_stylesheets=[dbc.themes.CYBORG], suppress_callback_exceptions=True)
manager = ProjectManager()

# JS: Добавлено предотвращение контекстного меню для ПКМ панорамирования
JS_SCRIPTS = """
<script>
    // Отключаем контекстное меню в графе, чтобы ПКМ работала как Pan
    document.addEventListener("contextmenu", function(e) {
        if (e.target.closest("#code-graph")) {
            e.preventDefault();
        }
    });

    window.dash_clientside = Object.assign({}, window.dash_clientside, {
        clientside: {
            toggleSidebar: function(n_clicks, selectedData, edgeData, width_data, is_open) {
                var ctx = dash_clientside.callback_context;
                var trigger = ctx.triggered.length > 0 ? ctx.triggered[0].prop_id : "";
                var new_state = is_open;
                
                if (trigger.includes("btn-toggle")) new_state = !is_open;
                else if (trigger.includes("code-graph") && (selectedData || edgeData)) new_state = true;

                var sb = document.getElementById("sidebar");
                var mc = document.getElementById("main-content");
                if (sb && mc) {
                    sb.style.transform = new_state ? "translateX(0)" : "translateX(-100%)";
                    mc.style.left = new_state ? width_data + "px" : "0px";
                }
                return new_state;
            },
            initResize: function(id) {
                setTimeout(function() {
                    var resizer = document.getElementById("resizer");
                    var sidebar = document.getElementById("sidebar");
                    var content = document.getElementById("main-content");
                    if (!resizer) return;
                    resizer.addEventListener("mousedown", function(e) {
                        e.preventDefault();
                        document.addEventListener("mousemove", resize);
                        document.addEventListener("mouseup", stopResize);
                    });
                    function resize(e) {
                        sidebar.style.width = e.clientX + "px";
                        content.style.left = e.clientX + "px";
                    }
                    function stopResize() {
                        document.removeEventListener("mousemove", resize);
                        document.removeEventListener("mouseup", stopResize);
                        window.dispatchEvent(new Event('resize'));
                    }
                }, 1000);
                return window.dash_clientside.no_update;
            }
        }
    });
</script>
"""

app.index_string = f'''
<!DOCTYPE html>
<html>
    <head>
        {{%metas%}}
        <title>CodeGraph</title>
        {{%favicon%}}
        {{%css%}}
        <style>
            html, body {{ height: 100%; margin: 0; overflow: hidden; background: {CFG['background_gradient']}; color: {CFG['text_main']}; font-family: 'Segoe UI'; }}
            .sidebar-container {{ position: fixed; top: 0; left: 0; bottom: 0; background: {CFG['sidebar_bg']}; border-right: 1px solid {CFG['sidebar_border']}; z-index: 1000; display: flex; flex-direction: column; transition: transform 0.3s ease; overflow: visible !important; }}
            .sidebar-content {{ padding: 0; overflow: hidden; height: 100%; display: flex; flex-direction: column; }}
            .tab-content {{ padding: 15px; overflow-y: auto; height: 100%; }}
            .sidebar-toggle-btn {{ position: absolute; top: 50%; right: -24px; width: 24px; height: 48px; transform: translateY(-50%); z-index: 2005; background: {CFG['sidebar_bg']}; border: 1px solid {CFG['sidebar_border']}; border-left: none; border-radius: 0 12px 12px 0; color: {CFG['accent_color']}; display: flex; align-items: center; justify-content: center; cursor: pointer; padding: 0; font-size: 18px; line-height: 1; box-shadow: 3px 0 6px rgba(0,0,0,0.2); transition: background-color 0.2s, color 0.2s; }}
            .sidebar-toggle-btn:hover {{ background-color: {CFG['node_bg_default']}; color: #fff; }}
            .custom-tabs {{ border-bottom: 1px solid {CFG['sidebar_border']}; }}
            .custom-tab {{ border: none !important; background-color: {CFG['sidebar_bg']} !important; color: {CFG['text_muted']} !important; padding: 10px !important; cursor: pointer; }}
            .custom-tab--selected {{ background-color: {CFG['input_bg']} !important; color: {CFG['accent_color']} !important; border-bottom: 2px solid {CFG['accent_color']} !important; }}
            .modern-input {{ background-color: {CFG['input_bg']} !important; border: 1px solid {CFG['input_border']} !important; color: {CFG['text_main']} !important; }}
            .modern-input:focus {{ border-color: {CFG['accent_color']} !important; }}
            .resizer {{ width: 5px; cursor: col-resize; position: absolute; top: 0; right: 0; bottom: 0; z-index: 1001; }}
            .resizer:hover {{ background: {CFG['accent_color']}; }}
            .main-content {{ position: absolute; top: 0; bottom: 0; right: 0; transition: left 0.1s; background: transparent; }}
            pre, code, .hljs {{ background: {CFG['code_bg']} !important; color: #dcdcdc !important; border: none !important; }}
            .hljs-string {{ color: #FF9D00 !important; }} 
            .hljs-keyword {{ color: #C678DD !important; }}
            .list-group-item {{ background: {CFG['input_bg']}; border-color: {CFG['input_border']}; color: {CFG['text_main']}; }}
            .list-group-item:hover {{ background: {CFG['node_bg_default']}; color: white; }}
            
            /* СТИЛИ ЛЕГЕНДЫ */
            .legend-item {{ display: flex; align-items: center; margin-bottom: 8px; font-size: 0.85rem; color: #ccc; }}
            .legend-icon {{ width: 14px; height: 14px; margin-right: 10px; border: 1px solid #555; }}
            .l-py {{ background: #3498DB; border-radius: 50%; }}
            .l-cpp {{ background: #E67E22; border-radius: 50%; }}
            .l-cls {{ background: #444; border-radius: 2px; border: 1px dashed #CF3721 !important; }}
            .l-file {{ background: {CFG['node_bg_default']}; border-radius: 2px; border: 1px dashed #777 !important; opacity: 0.5; }}
            .l-var {{ background: #1ABC9C; border-radius: 2px; }}
            .l-entry {{ background: #2ECC71; border-radius: 50%; border: 2px solid #fff; }}
        </style>
    </head>
    <body>
        {{%app_entry%}}
        <footer>{{%config%}}{{%scripts%}}{JS_SCRIPTS}{{%renderer%}}</footer>
    </body>
</html>
'''

graph_styles = [
    # Контейнеры
    {
        'selector': ':parent',
        'style': {
            'background-opacity': 0.05,
            'background-color': CFG['node_bg_default'],
            'border-width': 1,
            'border-color': '#777',
            'border-style': 'dashed',
            'content': 'data(label)',
            'text-valign': 'top',
            'color': '#999',
            'font-size': 10,
            'shape': 'roundrectangle'
        }
    },
    # Обычные ноды
    {'selector': 'node:childless', 'style': {'content': 'data(label)', 'color': '#ddd', 'font-size': 11, 'text-valign': 'center', 'text-halign': 'center', 'width': 45, 'height': 45}},
    {'selector': '.python-node', 'style': {'background-color': '#3498DB'}},
    {'selector': '.cpp-node', 'style': {'background-color': '#E67E22'}},
    {'selector': '.entry-point', 'style': {'background-color': '#2ECC71', 'width': 60, 'height': 60, 'border-width': 3, 'border-color': '#fff'}},
    {'selector': '.dunder', 'style': {'background-color': '#9B59B6', 'width': 35, 'height': 35}},
    {'selector': '.variable', 'style': {'background-color': '#1ABC9C', 'shape': 'rectangle', 'width': 40, 'height': 20}},
    {'selector': '.complex-code', 'style': {'border-width': 3, 'border-color': '#E74C3C'}},
    # Связи
    {'selector': 'edge', 'style': {'width': 2, 'line-color': CFG.get('edge_color', '#00BFFF'), 'target-arrow-color': CFG.get('edge_color', '#00BFFF'), 'target-arrow-shape': 'triangle', 'curve-style': 'bezier', 'opacity': 0.7}},
    {'selector': '.cross-file', 'style': {'line-style': 'dashed', 'width': 3, 'opacity': 0.9}},
    {'selector': '.var-usage', 'style': {'line-style': 'dotted', 'line-color': '#7F8C8D', 'target-arrow-color': '#7F8C8D', 'width': 1}},
    {'selector': 'edge:selected', 'style': {'width': 4, 'line-color': '#E74C3C', 'target-arrow-color': '#E74C3C'}},
]

# --- TABS ---

tab_explorer = html.Div(className='tab-content', children=[
    dbc.Row([
        dbc.Col(dbc.Button("←", id="btn-back", color="secondary", size="sm", outline=True), width=2),
        dbc.Col(dbc.Button("→", id="btn-fwd", color="secondary", size="sm", outline=True), width=2),
        dbc.Col(dbc.Button("📷", id="btn-save-img", color="success", size="sm"), width=2, className="ms-auto"),
    ], className="mb-3 g-1"),

    dbc.InputGroup([
        dbc.Input(id="input-dir", placeholder="Path...", className="modern-input"),
        dbc.Button("Load", id="btn-load", color="primary"),
    ], className="mb-3"),

    dbc.Input(id="search-input", placeholder="Search...", className="modern-input mb-2"),
    html.Div(id="search-results", style={'maxHeight': '100px', 'overflowY': 'auto', 'marginBottom': '15px'}),

    html.Hr(style={'borderColor': '#444'}),
    html.Div(id="node-info-box", children="Select elements..."),

    html.Div(className="mt-2 d-flex flex-column flex-grow-1", children=[
        html.Label("Code:", className="small text-muted"),
        html.Div(dcc.Markdown(id='code-display', style={'height': '100%', 'overflow': 'auto'}, highlight_config={'theme': 'dark'}),
                 style={'flex': '1', 'backgroundColor': CFG['code_bg'], 'border': '1px solid #444', 'borderRadius': '4px', 'padding': '5px'})
    ])
])

tab_settings = html.Div(className='tab-content', children=[
    html.Label("Filter:", className="text-muted"),
    dbc.Checklist(
        options=[{"label": "Functions", "value": "function"}, {"label": "Variables", "value": "variable"}, {"label": "Classes", "value": "class"}, {"label": "Dunder", "value": "dunder"}],
        value=["function", "variable", "class", "dunder"], id="filter-types", switch=True, className="mb-3 text-white"
    ),
    html.Hr(style={'borderColor': '#444'}),

    html.Label("Content Spread", className="text-muted mt-2"),
    dcc.Slider(id='setting-repulsion', min=1, max=5, step=1, value=3, marks={1:'Tight', 3:'Normal', 5:'Loose'}, tooltip={"placement": "bottom"}),
    html.Label("Edge Length", className="text-muted mt-4"),
    dcc.Slider(id='setting-edge-len', min=1, max=5, step=1, value=3, marks={1:'Short', 3:'Normal', 5:'Long'}, tooltip={"placement": "bottom"}),
    html.Label("Box Padding", className="text-muted mt-4"),
    dcc.Slider(id='setting-padding', min=1, max=5, step=1, value=2, marks={1:'Min', 5:'Max'}, tooltip={"placement": "bottom"}),
    html.Label("Box Spacing", className="text-muted mt-4"),
    dcc.Slider(id='setting-spacing', min=1, max=5, step=1, value=2, marks={1:'Close', 5:'Far'}, tooltip={"placement": "bottom"}),
    html.Hr(style={'borderColor': '#444'}),
    html.Label("Dimmed Opacity", className="text-muted mt-4"),
    dcc.Slider(id='setting-node-opacity', min=1, max=5, step=1, value=1, marks={1:'Faint', 5:'Visible'}, tooltip={"placement": "bottom"}),
    dcc.Slider(id='setting-edge-opacity', min=0, max=0.5, step=0.05, value=0.05, className="d-none"),
])

# --- НОВАЯ ВКЛАДКА HELP (ЛЕГЕНДА) ---
tab_help = html.Div(className='tab-content', children=[
    html.H4("Legend & Help", className="text-white mb-3"),

    html.Div([
        html.Div([html.Div(className="legend-icon l-py"), "Python Function"], className="legend-item"),
        html.Div([html.Div(className="legend-icon l-cpp"), "C++ Function"], className="legend-item"),
        html.Div([html.Div(className="legend-icon l-entry"), "Entry Point (main)"], className="legend-item"),
        html.Div([html.Div(className="legend-icon l-var"), "Variable"], className="legend-item"),
        html.Div([html.Div(className="legend-icon l-file"), "File / Module"], className="legend-item"),
        html.Div([html.Div(className="legend-icon l-cls"), "Class"], className="legend-item"),
    ], className="mb-4"),

    html.Hr(style={'borderColor': '#444'}),

    html.H6("Controls", className="text-muted"),
    html.Ul([
        html.Li("LMB: Select node/edge", className="small text-muted"),
        html.Li("Scroll: Zoom In/Out", className="small text-muted"),
        html.Li("Ctrl + Click: Select two nodes to find path", className="small text-muted"),
        html.Li("Drag Background: Select multiple (Box Selection)", className="small text-muted"),
    ], className="ps-3"),

    html.H6("Features", className="text-muted mt-3"),
    html.Div("Analyzes Python (AST) and C++ (Regex) codebases. Shows dependencies, variables, and code complexity.", className="small text-muted")
])

app.layout = html.Div([
    dcc.Store(id='sidebar-width-store', data=400),
    dcc.Store(id='is-open-store', data=True),
    dcc.Store(id='history-store', data=[]),
    dcc.Store(id='history-index', data=-1),

    html.Div(id='sidebar', className='sidebar-container', style={'width': '400px'}, children=[
        html.Button("‹", id="btn-toggle", className="sidebar-toggle-btn"),
        dcc.Tabs([
            dcc.Tab(label='Explorer', children=tab_explorer, className='custom-tab', selected_className='custom-tab--selected'),
            dcc.Tab(label='Settings', children=tab_settings, className='custom-tab', selected_className='custom-tab--selected'),
            dcc.Tab(label='Help', children=tab_help, className='custom-tab', selected_className='custom-tab--selected')
        ], className='custom-tabs', parent_className='sidebar-content'),
        html.Div(id='resizer', className='resizer')
    ]),

    html.Div(id='main-content', className='main-content', style={'left': '400px'}, children=[
        cyto.Cytoscape(
            id='code-graph',
            boxSelectionEnabled=True,
            layout={'name': 'cose', 'animate': True, 'fit': True, 'padding': 20},
            style={'width': '100%', 'height': '100%', 'background-color': 'transparent'},
            stylesheet=graph_styles,
            elements=[],
            responsive=True
        )
    ])
])

# --- CALLBACKS ---

app.clientside_callback(
    ClientsideFunction(namespace='clientside', function_name='toggleSidebar'),
    Output('is-open-store', 'data'),
    [Input('btn-toggle', 'n_clicks'), Input('code-graph', 'selectedNodeData'), Input('code-graph', 'tapEdgeData')],
    [State('sidebar-width-store', 'data'), State('is-open-store', 'data')],
    prevent_initial_call=True
)
app.clientside_callback(
    ClientsideFunction(namespace='clientside', function_name='initResize'),
    Output('sidebar-width-store', 'data'), Input('resizer', 'id')
)
@app.callback(Output('btn-toggle', 'children'), Input('is-open-store', 'data'))
def update_arrow(is_open): return "‹" if is_open else "›"

@app.callback(
    Output('code-graph', 'elements'),
    [Input('btn-load', 'n_clicks'), Input('input-dir', 'n_submit'), Input('filter-types', 'value')],
    State('input-dir', 'value'),
    prevent_initial_call=True
)
def load_and_filter(n_clk, n_sub, filters, path):
    if not path: return dash.no_update
    clean_path = path.strip('"').strip("'")
    if not os.path.exists(clean_path): return []
    manager.py_analyzer = PythonAnalyzer()
    raw_elements = manager.analyze(clean_path, allowed_langs=['python', 'cpp'])

    filtered, valid_ids = [], set()
    filters = filters or []
    for el in raw_elements:
        if 'source' not in el['data']:
            t = el['data'].get('type')
            if t in ['file', 'class', 'entry_point'] or t in filters:
                valid_ids.add(el['data']['id']); filtered.append(el)
    for el in raw_elements:
        if 'source' in el['data']:
            if el['data']['source'] in valid_ids and el['data']['target'] in valid_ids:
                filtered.append(el)
    return filtered

@app.callback(
    Output('search-results', 'children'),
    Input('search-input', 'value'),
    State('code-graph', 'elements')
)
def search(term, elements):
    if not term or len(term) < 2 or not elements: return []
    matches, limit = [], 0
    term = term.lower()
    for el in elements:
        if limit > 30: break
        if 'source' in el['data']: continue
        if term in el['data'].get('search_text', ''):
            matches.append(dbc.ListGroupItem(f"{el['data']['label']}", action=True, id={'type': 'search-item', 'index': el['data']['id']}, className="py-1"))
            limit+=1
    return dbc.ListGroup(matches)

@app.callback(
    Output('code-graph', 'layout'),
    [Input('setting-padding', 'value'), Input('setting-spacing', 'value'),
     Input('setting-repulsion', 'value'), Input('setting-edge-len', 'value')]
)
def update_layout_settings(padding, spacing, repulsion, edge_len):
    rep_map = {1: 100000, 2: 500000, 3: 1000000, 4: 2500000, 5: 5000000}
    len_map = {1: 20, 2: 40, 3: 60, 4: 100, 5: 150}
    pad_map = {1: 5, 2: 15, 3: 30, 4: 50, 5: 80}
    space_map = {1: 20, 2: 50, 3: 100, 4: 180, 5: 300}
    return {
        'name': 'cose', 'animate': True, 'randomize': False,
        'idealEdgeLength': len_map.get(edge_len, 50),
        'nodeRepulsion': rep_map.get(repulsion, 1000000),
        'nodeOverlap': 50, 'componentSpacing': space_map.get(spacing, 100),
        'gravity': 0.8, 'numIter': 1000, 'fit': True, 'padding': pad_map.get(padding, 30)
    }

@app.callback(
    Output('code-graph', 'generateImage'),
    Input('btn-save-img', 'n_clicks'),
    prevent_initial_call=True
)
def save_image(n): return {'type': 'jpeg', 'action': 'download', 'filename': 'code_graph'}

@app.callback(
    [Output('code-graph', 'stylesheet'),
     Output('code-display', 'children'),
     Output('node-info-box', 'children'),
     Output('history-store', 'data'),
     Output('history-index', 'data')],
    [Input('code-graph', 'selectedNodeData'),
     Input('code-graph', 'tapEdgeData'),
     Input('code-graph', 'tapNodeData'),
     Input({'type': 'search-item', 'index': ALL}, 'n_clicks'),
     Input('btn-back', 'n_clicks'),
     Input('btn-fwd', 'n_clicks'),
     Input('setting-node-opacity', 'value')],
    [State('code-graph', 'stylesheet'),
     State('code-graph', 'elements'),
     State('history-store', 'data'),
     State('history-index', 'data')]
)
def main_interaction(sel_nodes, tap_edge, tap_node, search_clk, btn_back, btn_fwd, node_op_lvl,
                     styles, elements, history, hist_idx):
    ctx = callback_context
    if not ctx.triggered: return styles, "", "Select...", history, hist_idx

    prop_id = ctx.triggered[0]['prop_id']
    target_ids, target_edge, mode = [], None, 'RESET'

    if 'tapNodeData' in prop_id and tap_node is None: mode = 'RESET'
    elif 'btn-back' in prop_id and hist_idx > 0:
        hist_idx -= 1; target_ids = [history[hist_idx]]; mode = 'NODE'
    elif 'btn-fwd' in prop_id and hist_idx < len(history) - 1:
        hist_idx += 1; target_ids = [history[hist_idx]]; mode = 'NODE'
    elif 'search-item' in prop_id:
        tid = ctx.triggered_id['index']; target_ids = [tid]; mode = 'NODE'
        if not history or history[hist_idx] != tid: history = history[:hist_idx+1] + [tid]; hist_idx += 1
    elif 'tapEdgeData' in prop_id and tap_edge:
        target_edge = tap_edge; mode = 'EDGE'
    elif 'selectedNodeData' in prop_id:
        if sel_nodes:
            target_ids = [n['id'] for n in sel_nodes]; mode = 'NODE'
            last_id = target_ids[-1]
            if not history or history[hist_idx] != last_id: history = history[:hist_idx+1] + [last_id]; hist_idx += 1
        else: mode = 'RESET'
    elif 'setting-' in prop_id:
        if sel_nodes: target_ids = [n['id'] for n in sel_nodes]; mode = 'NODE'
        elif tap_edge: target_edge = tap_edge; mode = 'EDGE'

    op_map = {1: 0.05, 2: 0.1, 3: 0.2, 4: 0.4, 5: 0.8}
    final_op = op_map.get(node_op_lvl, 0.1)

    if mode == 'RESET':
        return graph_styles, "", "Select node/edge...", history, hist_idx

    info, code, highlight_ids, path_edges = [], "", set(target_ids), set()

    if len(target_ids) == 2:
        start, end = target_ids[0], target_ids[1]
        adj = collections.defaultdict(list)
        for el in elements:
            if 'source' in el['data']: adj[el['data']['source']].append(el['data']['target'])
        queue, visited, found_path = [[start]], {start}, None
        while queue:
            path = queue.pop(0)
            if path[-1] == end: found_path = path; break
            for n in adj[path[-1]]:
                if n not in visited: visited.add(n); queue.append(list(path) + [n])
        if found_path:
            info.append(html.Div(f"Path: {len(found_path)} steps", className="text-success"))
            highlight_ids.update(found_path)
            for i in range(len(found_path)-1): path_edges.add(f"{found_path[i]}->{found_path[i+1]}")

    if mode == 'EDGE' and target_edge:
        code = f"```python\n{target_edge.get('snippet', '')}\n```"
        info.append(html.H5("Call", className="text-warning"))
        info.append(html.Div(f"{target_edge['source']} -> {target_edge['target']}"))
        highlight_ids.update([target_edge['source'], target_edge['target']])

    elif mode == 'NODE' and target_ids:
        main_node = next((e['data'] for e in elements if e['data']['id'] == target_ids[-1]), None)
        if main_node:
            lang = main_node.get('lang', '')
            code = f"```{lang}\n{main_node.get('code', '')}\n```"
            info.append(html.H4(main_node.get('name', 'Unknown'), className="text-info"))
            info.append(html.Div([
                dbc.Badge(f"LOC: {main_node.get('loc',0)}", color="dark", className="me-1"),
                dbc.Badge(f"Complexity: {main_node.get('complexity',0)}", color="danger" if main_node.get('complexity',0) > 10 else "success", className="me-1")
            ]))
            for el in elements:
                if 'source' in el['data']:
                    s, t = el['data']['source'], el['data']['target']
                    if s in target_ids: highlight_ids.add(t)
                    if t in target_ids: highlight_ids.add(s)

    new_style = list(graph_styles)
    new_style.append({'selector': 'node:childless', 'style': {'opacity': final_op}})
    new_style.append({'selector': 'edge', 'style': {'opacity': 0.1}})
    new_style.append({'selector': ':parent', 'style': {'border-opacity': final_op}})

    if highlight_ids:
        sel = ", ".join([f'node[id = "{x}"]' for x in highlight_ids])
        if sel: new_style.append({'selector': sel, 'style': {'opacity': 1, 'border-color': '#fff', 'border-width': 2}})

    for tid in target_ids:
        new_style.append({'selector': f'node[id = "{tid}"]', 'style': {'border-width': 4, 'border-color': '#F1C40F', 'opacity': 1}})

    for el in elements:
        if 'source' in el['data']:
            s, t = el['data']['source'], el['data']['target']
            eid = f"{s}->{t}"
            if eid in path_edges:
                new_style.append({'selector': f'edge[source="{s}"][target="{t}"]', 'style': {'opacity': 1, 'width': 6, 'line-color': '#FFD700', 'z-index': 999}})
            elif mode == 'EDGE' and target_edge and s == target_edge['source'] and t == target_edge['target']:
                new_style.append({'selector': f'edge[source="{s}"][target="{t}"]', 'style': {'opacity': 1, 'width': 4, 'line-color': '#E74C3C'}})
            elif s in highlight_ids and t in highlight_ids:
                new_style.append({'selector': f'edge[source="{s}"][target="{t}"]', 'style': {'opacity': 1}})

    return new_style, code, info, history, hist_idx

if __name__ == '__main__':
    app.run(debug=True)
