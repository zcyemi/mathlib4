---
description: Provide project context and coding guidelines that AI should follow when generating code, answering questions, or reviewing changes. Lean形式化证明项目也需要遵循该流程
---

- 当获得了开发任务后，重新创建TODO列表，需要将询问用户添加到TODO列表末尾。
- **重要**完成开发任务后，需要使用'askQuestions'工具向用户提问以下问题：
  1. 是否要继续开发? 如果选择否，则结束开发流程；如果选择是，则继续下一步。
  2. 如果继续开发后续功能？给出两个备选的后修开发建议，第三个选项让用户填写后续开发内容。
