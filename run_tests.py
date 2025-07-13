import os
import glob
import subprocess
import json
import sys

# --- 配置 ---
# C 测试文件所在的目录
C_TEST_DIR = '../c-testsuite/tests/single-exec'
# 您的编译器程序
COMPILER_EXE = '_build/default/bin/main.exe'
# 本地生成的 LLVM IR 文件名
LOCAL_LLVM_FILE = 'output.ll'
# 远程主机配置
REMOTE_HOST = 'ombp'
REMOTE_SANDBOX_DIR = 'sandbox/'
# 最终输出的 JSON 文件名
OUTPUT_JSON_FILE = 'test_results.json'

def run_command(command, stdin_content=None):
    """
    执行一个 shell 命令并返回其输出、错误和退出码。
    :param command: 命令列表 (e.g., ['ls', '-l'])
    :param stdin_content: 要传递给命令标准输入的内容 (字符串)
    :return: (stdout, stderr, exit_code)
    """
    print(f"  > Executing: {' '.join(command)}")
    try:
        # 如果有 stdin_content，我们通过管道传递它
        input_data = stdin_content # stdin_content.encode('utf-8') if stdin_content else None
        
        process = subprocess.run(
            command,
            input=input_data,
            capture_output=True,
            text=True,  # 将 stdout/stderr 解码为文本
            check=False # 不在返回码非0时抛出异常，我们手动处理
        )
        return process.stdout, process.stderr, process.returncode
    except FileNotFoundError:
        return "", f"Error: Command '{command[0]}' not found. Is it in your PATH?", 1
    except Exception as e:
        return "", f"An unexpected error occurred: {e}", 1


def main():
    """主执行函数"""
    # 检查编译器是否存在
    if not os.path.exists(COMPILER_EXE):
        print(f"Error: Compiler '{COMPILER_EXE}' not found. Please build your project first.", file=sys.stderr)
        sys.exit(1)
        
    # 确保远程沙箱目录存在
    print(f"Ensuring remote directory '~/sandbox' exists on '{REMOTE_HOST}'...")
    run_command(['ssh', REMOTE_HOST, f'mkdir -p {REMOTE_SANDBOX_DIR}'])

    # 查找所有的 .c 文件
    c_files = sorted(glob.glob(os.path.join(C_TEST_DIR, '*.c')))
    
    if not c_files:
        print(f"Error: No .c files found in '{C_TEST_DIR}'.", file=sys.stderr)
        sys.exit(1)

    c_files = c_files[:1]

    all_results = {}

    print(f"\nFound {len(c_files)} C files to test. Starting...")
    
    # 遍历每个 C 文件
    for c_file_path in c_files:
        filename = os.path.basename(c_file_path)
        print(f"\n--- Processing: {filename} ---")
        
        file_result = {}

        # 1. 编译 C 文件为 LLVM IR
        # 命令: % _build/default/bin/main.exe --verbose < [c_file_path]
        # 假设编译器读取 stdin 并将 LLVM IR 输出到 output.ll
        # 我们需要读取 C 文件内容并传递给 stdin
        try:
            with open(c_file_path, 'r') as f:
                c_code = f.read()
        except IOError as e:
            print(f"  ! Error reading file {c_file_path}: {e}")
            file_result['error'] = f"Failed to read source file: {e}"
            all_results[filename] = file_result
            continue

        compile_cmd = [COMPILER_EXE, '--verbose']
        # 这里的 stdout 是编译器的 --verbose 输出，stderr 可能是错误信息
        # 假设 main.exe 会自动创建 output.ll
        compile_stdout, compile_stderr, compile_exit_code = run_command(compile_cmd, stdin_content=c_code)
        
        file_result['compilation'] = {
            'command': f"{' '.join(compile_cmd)} < {c_file_path}",
            'verbose_output': compile_stdout.strip(),
            'stderr': compile_stderr.strip(),
            'exit_code': compile_exit_code
        }

        # 如果编译失败或未生成 output.ll，则跳过后续步骤
        if compile_exit_code != 0 or not os.path.exists(LOCAL_LLVM_FILE):
            print(f"  ! Compilation failed or '{LOCAL_LLVM_FILE}' not created. Skipping remote execution.")
            all_results[filename] = file_result
            continue

        # 2. scp 发送文件到远程主机
        # 命令: scp output.ll ombp:sandbox/
        remote_path = f"{REMOTE_HOST}:{REMOTE_SANDBOX_DIR}"
        scp_cmd = ['scp', LOCAL_LLVM_FILE, remote_path]
        scp_stdout, scp_stderr, scp_exit_code = run_command(scp_cmd)

        file_result['scp'] = {
            'command': ' '.join(scp_cmd),
            'stdout': scp_stdout.strip(),
            'stderr': scp_stderr.strip(),
            'exit_code': scp_exit_code
        }

        if scp_exit_code != 0:
            print(f"  ! SCP failed. Skipping remote execution.")
            all_results[filename] = file_result
            continue

        # 3. ssh 在远程主机上执行 lli 并获取结果
        # 命令: ssh ombp "lli ~/sandbox/output.ll;echo $?"
        remote_ll_path = os.path.join(REMOTE_SANDBOX_DIR, os.path.basename(LOCAL_LLVM_FILE))
        # 在远程执行的命令
        remote_exec_str = f"lli {remote_ll_path}; echo $?"
        ssh_cmd = ['ssh', REMOTE_HOST, remote_exec_str]
        
        ssh_stdout, ssh_stderr, ssh_exit_code = run_command(ssh_cmd)

        # 解析 ssh 的输出：最后一行是 lli 的退出码，其余是 lli 的标输出
        lli_output_lines = ssh_stdout.strip().split('\n')
        lli_exit_code = -1  # 默认值
        lli_stdout = ""

        if lli_output_lines and lli_output_lines[-1].isdigit():
            lli_exit_code = int(lli_output_lines[-1])
            lli_stdout = "\n".join(lli_output_lines[:-1])
        else:
            # 如果输出为空或最后一行不是数字，则都视为 lli 的输出
            lli_stdout = ssh_stdout.strip()

        file_result['remote_execution'] = {
            'command': ' '.join(ssh_cmd),
            'lli_stdout': lli_stdout,
            'lli_exit_code': lli_exit_code,
            'ssh_stderr': ssh_stderr.strip(), # ssh 本身的错误
            'ssh_exit_code': ssh_exit_code
        }
        
        all_results[filename] = file_result

    # 清理本地生成的 output.ll
    if os.path.exists(LOCAL_LLVM_FILE):
        os.remove(LOCAL_LLVM_FILE)
        print(f"\nCleaned up local file: {LOCAL_LLVM_FILE}")

    # 将所有结果写入 JSON 文件
    with open(OUTPUT_JSON_FILE, 'w', encoding='utf-8') as f:
        json.dump(all_results, f, indent=4, ensure_ascii=False)

    print(f"\n✅ All done! Results have been saved to '{OUTPUT_JSON_FILE}'.")


if __name__ == '__main__':
    main()
